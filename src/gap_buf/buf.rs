use std::{marker::PhantomData, ops::RangeBounds, ptr::NonNull};

use crate::{
    grower::Grower,
    raw_gap_buf::RawGapBuf,
    utils::{get_parts_at, get_range},
};

use super::drain::Drain;

#[derive(Clone)]
struct GrowingGapBuf<T, G: Grower<[T]>> {
    raw: RawGapBuf<T>,
    grower: G,
}

impl<T, G: Grower<[T]>> GrowingGapBuf<T, G> {
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

    #[inline(always)]
    pub fn with_grower(grower: G) -> Self {
        Self {
            raw: Default::default(),
            grower,
        }
    }

    #[inline(always)]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.raw.get(index)
    }

    #[inline(always)]
    pub fn get_slice<RB: RangeBounds<usize>>(&self, r: RB) -> Option<[&[T]; 2]> {
        let r = get_range(self.raw.len(), r)?;
        self.raw.get_slice(r)
    }

    #[inline(always)]
    #[allow(clippy::wrong_self_convention)]
    pub fn to_slice(&mut self) -> &[T] {
        self.raw.to_slice()
    }

    #[inline(always)]
    pub fn to_slice_mut(&mut self) -> &mut [T] {
        self.raw.to_slice_mut()
    }

    #[inline]
    pub fn insert(&mut self, at: usize, val: T) {
        assert!(self.raw.get(at).is_some() || self.raw.len() == at);
        if self.raw.gap_len() == 0 {
            let [start, end] = self.raw.get_parts();
            let base = self.grower.base_gap_size(start, end);
            let max = self.grower.max_gap_size(start, end);
            self.realloc_gap_at(base.min(max) + 1, at);
        }
        self.raw.move_gap_start_to(at);

        // SAFETY: the target location should never have a value as it is in the gap
        unsafe {
            self.raw.spare_capacity_mut().cast::<T>().write(val);
            // we have written the value and it is now safe to grow the start
            self.raw.grow_start(1);
        }
    }

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

    /// Reallocate the buffer with the provided gap size
    ///
    /// Generally [`GrowingGapBuf::realloc_gap_at`] should be preferred instead as in most cases of
    /// reallocation, the goal is to allocate enough space to before an insertion is performed.
    ///
    /// This is allows growing or shrinking the gap without any knowledge of the insertions size
    /// (such as an iterator of T's).
    pub(crate) fn realloc(&mut self, gap_size: usize) {
        let [start, end] = self.raw.get_parts();
        // SAFETY: since we are reallocating the buffer we do not want to call any drop code and we
        // are dropping the previous buffer to avoid accidental access or drop code being called
        self.raw = unsafe { RawGapBuf::new_with_slice(&[start], gap_size, &[end]) };
    }

    /// Reallocate the buffer and position the gap start at the provided position
    ///
    /// When performing an insertion we reserve enough space for the insertion, move the gap to a
    /// specific posiiton and copy the value over.
    ///
    /// Instead of that, this method makes the "move the gap" step a part of the copying step.
    /// Rather than shifting around T's we just allocate accounting for the requested position
    /// meaning element shifting isn't performed.
    pub(crate) fn realloc_gap_at(&mut self, gap_size: usize, at: usize) {
        let [start, end] = self.raw.get_parts();
        let temp;
        let temp2;
        let (left, right) = {
            let (start, mid, end, before_mid) = get_parts_at(start, end, at);
            if before_mid {
                temp2 = [mid, end];
                temp = [start];
                (temp.as_slice(), temp2.as_slice())
            } else {
                temp2 = [start, mid];
                temp = [end];
                (temp2.as_slice(), temp.as_slice())
            }
        };
        // SAFETY: since we are reallocating the buffer we do not want to call any drop code and we
        // are dropping the previous buffer to avoid accidental access or drop code being called
        self.raw = unsafe { RawGapBuf::new_with_slice(left, gap_size, right) };
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
}
