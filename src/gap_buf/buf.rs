use std::{marker::PhantomData, ops::RangeBounds, ptr::NonNull};

use crate::{grower::Grower, raw_gap_buf::RawGapBuf, utils::get_range};

use super::drain::Drain;

#[derive(Clone)]
pub struct GrowingGapBuf<T, G: Grower<[T]>> {
    raw: RawGapBuf<T>,
    grower: G,
}

impl<T, G: Grower<[T]> + Default> Default for GrowingGapBuf<T, G> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, G: Grower<[T]>> GrowingGapBuf<T, G> {
    /// Initialize an empty gap buffer
    #[inline(always)]
    pub fn new() -> GrowingGapBuf<T, G>
    where
        G: Default,
    {
        Self {
            raw: RawGapBuf::default(),
            grower: G::default(),
        }
    }

    /// Initialize a gap buffer with the provided grower
    ///
    /// Depending on the type and use case you may prefer a different strategy when growing
    /// or shrinking the gap buffer. This allows you to provide your own [`Grower`] to limit how
    /// much extra capacity can be allocated.
    #[inline(always)]
    pub fn with_grower(grower: G) -> Self {
        Self {
            raw: Default::default(),
            grower,
        }
    }

    /// Returns the total length of the buffer excluding the gap length
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.raw.len()
    }

    /// Returns the gap length
    ///
    /// This is the same as [`Vec::capacity`] but for a gap buffer.
    #[inline(always)]
    pub fn gap_len(&self) -> usize {
        self.raw.gap_len()
    }

    /// Moves the gap out of the provided range
    ///
    /// Returns without modifying the gap if it can already be contiguously read.
    #[inline]
    pub fn move_gap_out_of<RB: RangeBounds<usize>>(&mut self, r: RB) {
        let r = get_range(self.len(), r).expect("provided ranges should never be out of bounds");
        self.raw.move_gap_out_of(r);
    }

    /// Moves the gap's start to the provided position
    ///
    /// # Panics
    /// Panics if the provided position > len.
    #[inline]
    pub fn move_gap_start_to(&mut self, to: usize) {
        self.raw.move_gap_start_to(to);
    }

    /// Get the value at the provided index
    ///
    /// This will account for the gap so you must provide the index as if you were indexing into a
    /// normal slice.
    ///
    /// Returns None if index is out of bounds.
    #[inline(always)]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.raw.get(index)
    }

    /// Get the value at the provided index
    ///
    /// Same as [`GrowingGapBuf::get`] but returns mutable reference to T.
    #[inline(always)]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.raw.get_mut(index)
    }

    /// Get slices of the values in the range
    ///
    /// If the provided range is not out of bounds, returns two slices of T.
    /// The first one being before the gap, and the second one being after the gap.
    ///
    /// If a single slice is needed [`GrowingGapBuf::get_slice`] can be used.
    #[inline(always)]
    pub fn get_range<RB: RangeBounds<usize>>(&self, r: RB) -> Option<[&[T]; 2]> {
        let r = get_range(self.raw.len(), r)?;
        self.raw.get_range(r)
    }

    /// Get a slice of the values in the range
    ///
    /// If the provided range is not out of bounds, returns a slice of T.
    ///
    /// This method will perform the minimum copies needed to get a contiguous slice.
    ///
    /// Calling this method can be expensive with a small gap, large range or disjointed multiple
    /// reads. [`RawGapBuf::get_range`] should be preferred whenever possible.
    #[inline(always)]
    pub fn get_slice<RB: RangeBounds<usize>>(&mut self, r: RB) -> Option<&mut [T]> {
        let r = get_range(self.raw.len(), r)?;
        self.raw.get_slice(r)
    }

    /// Get the left and right side of the gap buffer
    #[inline(always)]
    pub fn get_parts(&self) -> [&[T]; 2] {
        self.raw.get_parts()
    }

    /// Get the left and right side of the gap buffer as mutable slices
    #[inline(always)]
    pub fn get_parts_mut(&mut self) -> [&mut [T]; 2] {
        self.raw.get_parts_mut()
    }

    /// Shift's the T's to one side and returns a slice of T's
    ///
    /// Calling this method isn't recommended as it requires shifting all of the elements to the
    /// end or start of the buffer. Prefer [`GrowingGapBuf::get_range`] whenever possible. If you
    /// strictly need need a contiguous slice, but only for a specific range, use
    /// [`GrowingGapBuf::get_slice`] instead.
    #[inline(always)]
    #[allow(clippy::wrong_self_convention)]
    pub fn to_slice(&mut self) -> &[T] {
        self.raw.to_slice()
    }

    /// Same as [`GrowingGapBuf::to_slice`] but returns a mutable slice
    ///
    /// See [`GrowingGapBuf::to_slice`] for more information.
    #[inline(always)]
    pub fn to_slice_mut(&mut self) -> &mut [T] {
        self.raw.to_slice_mut()
    }

    /// Insert T at the provided position
    ///
    /// # Panics if the provided position is out of bounds.
    #[inline]
    pub fn insert(&mut self, at: usize, val: T) {
        assert!(self.raw.get(at).is_some() || self.raw.len() == at);
        if self.raw.gap_len() == 0 {
            let [start, end] = self.raw.get_parts();
            let base = self.grower.base_gap_size(start, end);
            let max = self.grower.max_gap_size(start, end);
            self.grow_gap_at(base.min(max) + 1, at);
        } else {
            self.raw.move_gap_start_to(at);
        }

        // SAFETY: the target location should never have a value as it is in the gap
        unsafe {
            self.raw.spare_capacity_mut().cast::<T>().write(val);
            // we have written the value and it is now safe to grow the start
            self.raw.grow_start(1);
        }
    }

    /// Insert many T's from an iterator at the provided position
    ///
    /// This is the [`Extend`] of a gap buffer. Unlike the trait this accepts an insert position
    /// since inserts are expected to not be at the end in most cases. To push the items to the end
    /// of the buffer the buffers length can be provided as the position.
    ///
    /// # Panics
    /// If the provided position > len panics.
    #[inline]
    pub fn insert_many<I: Iterator<Item = T>>(&mut self, mut iter: I, at: usize) {
        let mut hint = iter.size_hint().0;
        self.raw.move_gap_start_to(at);
        while let Some(item) = iter.next() {
            if self.raw.gap_len() < hint {
                self.grow_gap(hint.max(1));
            }

            // SAFETY: we have moved the gap to the first T position in the gap, each item we add
            // shifts it by one. we have also growed the gap to account for the insert.
            // It is now safe to write the T and grow our start slice
            unsafe {
                self.raw
                    .start_ptr_mut()
                    .add(self.raw.start_len())
                    .write(item);
                // The grow is intentionally adjusted on every iteration as we are calling user code which
                // could panic and leave our buffer in an invalid state.
                self.raw.grow_start(1);
            };
            hint = iter.size_hint().0;
        }
    }

    /// Drains the provided range from the gap buffer
    ///
    /// If the provided ranges are out of bounds returns None.
    /// The drain is an [`Iterator`] of owned T's. Usage wise this is the same as [`Vec::drain`]
    /// except for gap buffers.
    ///
    /// See [`Drain`] for its available methods.
    #[inline(always)]
    pub fn drain<RB: RangeBounds<usize>>(&mut self, r: RB) -> Option<Drain<'_, T>> {
        let r = get_range(self.raw.len(), r)?;
        self.raw.move_gap_start_to(r.end);
        let ret = Some(Drain {
            // SAFETY: we have done the necessary range checks and have moved the gap start
            // position to the end of the provided range
            // this means the pointer points to a valid [T] starting at r.start and ending at
            // r.end
            ptr: unsafe {
                NonNull::slice_from_raw_parts(self.raw.start_ptr().add(r.start), r.len())
            },
            __p: PhantomData,
        });

        // SAFETY: the shrunken portion of the start slice is moved into Drain
        // this part is now considered removed by the buffer
        // we have also done the necessary range checks above, and moved the gap to the end of the range
        // it is now safe safe to shrink as Drain has taken ownership of this portion of the buffer
        unsafe { self.raw.shrink_start(r.len()) };

        ret
    }

    /// See [`RawGapBuf::realloc`]
    pub(crate) fn grow_gap(&mut self, by: usize) {
        self.raw.grow_gap(by);
    }

    /// See [`RawGapBuf::realloc_gap_at`]
    pub(crate) fn grow_gap_at(&mut self, by: usize, at: usize) {
        self.raw.grow_gap_at(by, at);
    }
}

impl<T, G: Grower<[T]>> Drop for GrowingGapBuf<T, G> {
    fn drop(&mut self) {
        // SAFETY: after calling this function self cannot be reused
        // it is safe to drop the inner values
        unsafe { self.raw.drop_t() };
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;
    use rstest_reuse::apply;

    use crate::grower::test_utils::*;

    use super::GrowingGapBuf;

    type GapBuf = GrowingGapBuf<String, TestGrower>;

    fn fill_gap_buf<G: Grower<[String]>>(gap_buf: &mut GrowingGapBuf<String, G>) {
        for (i, item) in ["1", "2", "3", "4", "5", "6"]
            .map(String::from)
            .into_iter()
            .enumerate()
        {
            gap_buf.insert(i, item);
        }
    }

    #[apply(grower_template)]
    fn insert(#[case] g: TestGrower) {
        let mut s_buf = GapBuf::with_grower(g);

        s_buf.insert(0, String::from("Hi"));
        assert_eq!(s_buf.get(0).map(String::as_str), Some("Hi"));
        assert_eq!(s_buf.get(1), None);
        assert_eq!(s_buf.get(2), None);

        s_buf.insert(0, String::from("Bye"));
        assert_eq!(s_buf.get(0).map(String::as_str), Some("Bye"));
        assert_eq!(s_buf.get(1).map(String::as_str), Some("Hi"));
        assert_eq!(s_buf.get(2), None);
        assert_eq!(s_buf.get(3), None);

        s_buf.insert(2, String::from("World"));
        assert_eq!(s_buf.get(0).map(String::as_str), Some("Bye"));
        assert_eq!(s_buf.get(1).map(String::as_str), Some("Hi"));
        assert_eq!(s_buf.get(2).map(String::as_str), Some("World"));
        assert_eq!(s_buf.get(3), None);
        assert_eq!(s_buf.get(4), None);
    }

    #[apply(grower_template)]
    fn insert_many(#[case] g: TestGrower) {
        let mut s_buf = GapBuf::with_grower(g);
        s_buf.insert_many([1, 2, 3, 4].map(|n| n.to_string()).into_iter(), 0);
        assert_eq!(
            s_buf.get_parts(),
            [["1", "2", "3", "4"].as_slice(), [].as_slice()]
        );

        s_buf.insert_many(["a", "b", "c", "d"].map(|n| n.to_string()).into_iter(), 2);
        assert_eq!(
            s_buf.get_parts(),
            [
                ["1", "2", "a", "b", "c", "d"].as_slice(),
                ["3", "4"].as_slice()
            ]
        );
    }

    #[apply(grower_template)]
    fn drain(#[case] g: TestGrower) {
        let mut s_buf = GapBuf::with_grower(g);
        for (i, val) in ["1", "2", "3"].map(String::from).into_iter().enumerate() {
            s_buf.insert(i, val);
        }
        let sample = s_buf.clone();

        let drain = s_buf.drain(0..2).unwrap();
        assert_eq!(drain.as_slice(), &["1", "2"]);
        drop(drain);
        assert_eq!(s_buf.get(0).unwrap(), "3");
        assert_eq!(s_buf.get(1), None);
        assert_eq!(s_buf.get(2), None);
        assert_eq!(s_buf.to_slice(), &["3"]);

        let drain = s_buf.drain(0..0).unwrap();
        assert_eq!(drain.as_slice(), ([] as [String; 0]).as_slice());

        let mut s_buf = sample.clone();
        let drain = s_buf.drain(0..3).unwrap();
        let v = Vec::from_iter(drain);
        assert_eq!(v, &["1", "2", "3"]);
        s_buf.insert(0, String::from("4"));
        assert_eq!(s_buf.get(0).unwrap(), "4");
        assert_eq!(s_buf.get(1), None);
        assert_eq!(s_buf.get(2), None);
        assert_eq!(s_buf.to_slice(), &["4"]);
    }

    #[apply(grower_template)]
    fn drain_iter(#[case] g: TestGrower) {
        let mut s_buf = GapBuf::with_grower(g);
        for (i, val) in ["1", "2", "3", "4"]
            .map(String::from)
            .into_iter()
            .enumerate()
        {
            s_buf.insert(i, val);
        }
        let sample = s_buf.clone();

        let mut drain_iter = s_buf.drain(0..4).unwrap();
        assert_eq!(drain_iter.next_back().unwrap(), "4");
        assert_eq!(drain_iter.next_back().unwrap(), "3");
        assert_eq!(drain_iter.next().unwrap(), "1");
        assert_eq!(drain_iter.next().unwrap(), "2");
        assert!(drain_iter.next().is_none());
        assert!(drain_iter.next_back().is_none());

        let mut s_buf = sample.clone();
        let mut drain_iter = s_buf.drain(1..4).unwrap();
        assert_eq!(drain_iter.nth(1).unwrap(), "3");
        #[allow(clippy::iter_nth_zero)]
        {
            assert_eq!(drain_iter.nth(0).unwrap(), "4");
            assert_eq!(drain_iter.nth(0), None);
            assert_eq!(drain_iter.nth(1), None);
        }
        assert_eq!(drain_iter.nth(2), None);

        let mut s_buf = sample.clone();
        let drain_iter = s_buf.drain(0..4).unwrap();
        assert_eq!(drain_iter.count(), 4);
    }

    #[apply(grower_template)]
    fn get(g: TestGrower) {
        let mut s_buf = GrowingGapBuf::with_grower(g);
        for (i, item) in ["1", "2", "3", "4", "5", "6"]
            .map(String::from)
            .into_iter()
            .enumerate()
        {
            s_buf.insert(i, item);
        }

        assert_eq!(s_buf.get(0).unwrap(), "1");
        assert_eq!(s_buf.get(1).unwrap(), "2");
        assert_eq!(s_buf.get(2).unwrap(), "3");
        assert_eq!(s_buf.get(3).unwrap(), "4");
        assert_eq!(s_buf.get(4).unwrap(), "5");
        assert_eq!(s_buf.get(5).unwrap(), "6");
        assert_eq!(s_buf.get(6), None);
        assert_eq!(s_buf.get(7), None);
    }

    #[apply(grower_template)]
    fn get_range(g: TestGrower) {
        let mut s_buf = GrowingGapBuf::with_grower(g);
        fill_gap_buf(&mut s_buf);

        assert_eq!(
            s_buf.get_range(0..6).unwrap(),
            [["1", "2", "3", "4", "5", "6"].as_slice(), &[]]
        );

        assert_eq!(s_buf.get_range(1..3).unwrap(), [["2", "3"].as_slice(), &[]]);

        s_buf.raw.move_gap_start_to(1);

        assert_eq!(
            s_buf.get_range(0..3).unwrap(),
            [["1"].as_slice(), ["2", "3"].as_slice()]
        );

        assert_eq!(s_buf.get_range(0..7), None);
    }

    #[apply(grower_template)]
    fn get_slice(g: TestGrower) {
        let mut s_buf = GrowingGapBuf::with_grower(g);
        fill_gap_buf(&mut s_buf);

        assert_eq!(
            s_buf.get_slice(0..6).unwrap(),
            ["1", "2", "3", "4", "5", "6"]
        );

        assert_eq!(s_buf.get_slice(1..3).unwrap(), ["2", "3"].as_slice());

        s_buf.raw.move_gap_start_to(1);

        assert_eq!(s_buf.get_slice(0..3).unwrap(), ["1", "2", "3"].as_slice());

        assert_eq!(s_buf.get_range(0..7), None);
    }
}
