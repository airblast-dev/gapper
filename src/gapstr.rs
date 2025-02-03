use std::{
    cmp::Ordering,
    marker::PhantomData,
    ops::{Deref, DerefMut, Range, RangeBounds},
    str::{from_utf8_unchecked, from_utf8_unchecked_mut, Chars},
};

use bytemuck::{cast_slice, must_cast_slice};

use crate::{
    grower::{DefaultGrower, Grower},
    raw_gap_buf::RawGapBuf,
    utils::{get_range, u8_is_char_boundary},
};

pub type GapString = GrowingGapString<DefaultGrower>;

#[derive(Clone)]
pub struct GrowingGapString<G: Grower<str>> {
    buf: RawGapBuf<u8>,
    grower: G,
}

impl<G: Grower<str> + Default> Default for GrowingGapString<G> {
    fn default() -> Self {
        Self::new()
    }
}

impl<G: Grower<str>> GrowingGapString<G> {
    /// Initialize an empty [`GrowingGapString`]
    #[inline]
    pub fn new() -> Self
    where
        G: Default,
    {
        Self {
            buf: RawGapBuf::new(),
            grower: Default::default(),
        }
    }

    /// Initialize an empty [`GrowingGapString`] with a [`Grower`]
    #[inline]
    pub const fn with_grower(grower: G) -> Self {
        Self {
            buf: RawGapBuf::new(),
            grower,
        }
    }

    /// Initialize a [`GrowingGapString`] using multiple string slices and a gap size.
    #[inline]
    pub fn from_slices(start: &[&str], gap_size: usize, end: &[&str]) -> Self
    where
        G: Default,
    {
        let grower = G::default();
        Self {
            buf: unsafe {
                RawGapBuf::new_with_slice(
                    core::mem::transmute::<&[&str], &[&[u8]]>(start),
                    gap_size,
                    core::mem::transmute::<&[&str], &[&[u8]]>(end),
                )
            },
            grower,
        }
    }

    /// Returns the total length excluding the gap
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.buf.len()
    }

    /// Returns the gaps length
    #[inline(always)]
    pub fn gap_len(&self) -> usize {
        self.buf.gap_len()
    }

    /// Returns true if the buffer is empty
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Same as [`str::get`] but for gap buffers
    ///
    /// Returns None if the range is out of bounds or is not on a char boundary.
    #[inline]
    pub fn get<RB: RangeBounds<usize>>(&self, r: RB) -> Option<[&str; 2]> {
        let r = get_range(self.buf.len(), r)?;
        if !self.is_get_char_boundary(r.start..r.end) {
            return None;
        }

        let [start, end] = self.buf.get_range(r)?;
        unsafe { Some([from_utf8_unchecked(start), from_utf8_unchecked(end)]) }
    }

    /// Same as [`str::get_mut`] but for gap buffers
    ///
    /// Returns None if the range is out of bounds or is not on a char boundary.
    #[inline]
    pub fn get_mut<RB: RangeBounds<usize>>(&mut self, r: RB) -> Option<[&mut str; 2]> {
        let r = get_range(self.buf.len(), r)?;
        if !self.is_get_char_boundary(r.start..r.end) {
            return None;
        }

        let [start, end] = self.buf.get_range_mut(r)?;
        unsafe { Some([from_utf8_unchecked_mut(start), from_utf8_unchecked_mut(end)]) }
    }

    /// Returns a contigious slice from the gap buffer
    ///
    /// The slice is constructed by shifting the elements to a position that leaves the requested
    /// range as a single slice. This isn't recommended as it will move the gap and can have a
    /// large cost in some cases. Prefer [`GrowingGapString::get`] wherever possible.
    ///
    /// Returns None if the range is out of bounds or is not on a char boundary.
    #[inline]
    pub fn get_slice<RB: RangeBounds<usize>>(&mut self, r: RB) -> Option<&str> {
        let r = get_range(self.buf.len(), r)?;
        if !self.is_get_char_boundary(r.start..r.end) {
            return None;
        }
        let s = self.buf.get_slice(r)?;
        // SAFETY: we have checked if the range is on a char boundary above
        unsafe { Some(from_utf8_unchecked(s)) }
    }

    /// Returns a contigious slice from the gap buffer
    ///
    /// Same as [`GrowingGapString::get_slice`] but returns a mutable reference.
    #[inline]
    pub fn get_slice_mut<RB: RangeBounds<usize>>(&mut self, r: RB) -> Option<&mut str> {
        let r = get_range(self.buf.len(), r)?;
        if !self.is_get_char_boundary(r.start..r.end) {
            return None;
        }
        let s = self.buf.get_slice(r)?;
        // SAFETY: we have checked if the range is on a char boundary above
        unsafe { Some(from_utf8_unchecked_mut(s)) }
    }

    /// Returns both sides of the gap buffer
    #[inline(always)]
    pub fn get_parts(&self) -> [&str; 2] {
        self.buf.get_parts().map(|s| unsafe {
            // SAFETY: we do not allow the gap to be positioned between char boundaries both
            // parts are always valid UTF-8 string slice
            from_utf8_unchecked(s)
        })
    }

    /// Returns both sides of the gap buffer as mutable slices
    #[inline(always)]
    pub fn get_parts_mut(&mut self) -> [&str; 2] {
        self.buf.get_parts_mut().map(|s| unsafe {
            // SAFETY: we do not allow the gap to be positioned between char boundaries both
            // parts are always valid UTF-8 string slice
            from_utf8_unchecked(s)
        })
    }

    #[inline(always)]
    fn is_get_char_boundary(&self, r: Range<usize>) -> bool {
        // TODO: this a mess
        self.buf
            .get(r.start)
            .copied()
            .is_some_and(u8_is_char_boundary)
            && (self.buf.get(r.end).is_none()
                || self
                    .buf
                    .get(r.end)
                    .copied()
                    .is_some_and(u8_is_char_boundary))
            || (r.start == r.end && self.buf.len() >= r.start)
    }

    /// Insert a string at the provided position
    ///
    /// # Panics
    /// If the provided position is greater than [`GrowingGapString::len`] or the position is not
    /// on a char boundary.
    pub fn insert(&mut self, s: &str, at: usize) {
        assert!(
            self.buf.get(at).copied().is_some_and(u8_is_char_boundary) || self.buf.len() == at,
            "insertion should always be on a char boundary"
        );
        // polonius moment
        // can't use [`GrowingGapString::get_parts`] as borrow checker can't infer that the grower
        // field and slices are unrelated in regards to mutability.
        let [start, end] = self.buf.get_parts().map(|s| unsafe {
            // SAFETY: we do not allow the gap to be positioned between char boundaries both
            // parts are always valid UTF-8 string slice
            from_utf8_unchecked(s)
        });
        if self.buf.gap_len() < s.len() {
            let base_gap_size = self
                .grower
                .base_gap_size(start, end)
                .min(self.grower.max_gap_size(start, end));
            self.buf.grow_gap(base_gap_size + s.len());
        }
        self.buf.move_gap_start_to(at);

        let [_, gap, _] = self.buf.get_parts_as_uninit();

        gap[0..s.len()].copy_from_slice(must_cast_slice(s.as_bytes()));

        unsafe {
            // SAFETY: we have initialized the gaps first s.len items it is now safe to grow the
            // start
            self.buf.grow_start(s.len());
        };
    }

    /// Equivalent to [`String::drain`] from the standard library
    ///
    /// Returns an iterator of char's, but unlike the standard library this shifts the gap to the
    /// end of the provided range and shrinks the start slice. Rather than shifting on each
    /// [`Iterator::next`] call, this shifts elements once and is cheap to use relative to
    /// [`String::drain`].
    ///
    /// # Panics
    /// If the provided range is out of bounds or the range start is greater than its end.
    /// If the range does not lie on a char boundary.
    pub fn drain<RB: RangeBounds<usize>>(&mut self, r: RB) -> Drain {
        let r = get_range(self.buf.len(), r)
            .expect("range should never be out of bounds when draining");
        assert!(self.is_get_char_boundary(r.start..r.end));

        {
            let [start, end] = self
                .buf
                .get_parts()
                .map(|s| unsafe { from_utf8_unchecked(s) });

            let max_gap_size = self.grower.max_gap_size(start, end);
            let gap_len = self.gap_len();
            if gap_len > max_gap_size {
                let base_gap_size = self.grower.base_gap_size(start, end);
                self.shrink_gap(gap_len - max_gap_size.min(base_gap_size));
            }
        }

        self.buf.move_gap_start_to(r.end);
        // SAFETY:
        // - s is valid as long as self isn't mutated which we dissallow via the PhantomData in Drain
        // - The start slice is fully initialized and we have validated the range above
        //
        // WARNING: until we return the Drain, we are technically allowed to call mutable methods,
        // but calling any method with &mut self is unsound if it moves anything inside the
        // allocation. When editing this code make sure that no moves or copies are made after the
        // string variable is initialized.
        unsafe {
            let s: &str =
                from_utf8_unchecked(self.buf.start().as_ref().get_unchecked(r.start..r.end));
            self.buf.shrink_start(r.len());
            Drain {
                chars: s.chars(),
                __p: PhantomData,
            }
        }
    }

    /// Equivalent to [`String::replace_range`] from the standard library
    ///
    /// # Panics
    /// If the provided range is out of bounds or the range start is greater than its end.
    /// If the range does not lie on a char boundary.
    pub fn replace_range<RB: RangeBounds<usize>>(&mut self, r: RB, s: &str) {
        let r = get_range(self.buf.len(), r).expect("out of bounds range for replace_range");
        assert!(self.is_get_char_boundary(r.start..r.end));
        match r.len().cmp(&s.len()) {
            Ordering::Greater => {
                self.buf.move_gap_start_to(r.end);
                // SAFETY: we just checked the bounds above
                self.buf.get_parts_mut()[0][r.start..r.start + s.len()]
                    .copy_from_slice(s.as_bytes());
                // SAFETY: we checked the bounds above and r.len is greater than s.len so no
                // overflow can occur
                unsafe {
                    self.buf.shrink_start(r.len() - s.len());
                }
            }
            Ordering::Less => {
                let needed_space = s.len() - r.len();
                if self.buf.gap_len() < needed_space {
                    let [start, end] = self
                        .buf
                        .get_parts()
                        .map(|s| unsafe { from_utf8_unchecked(s) });
                    let base_gap_size = self.grower.base_gap_size(start, end);
                    self.buf.grow_gap(needed_space + base_gap_size);
                }

                self.buf.move_gap_start_to(r.end);
                let [start, gap, _] = self.buf.get_parts_as_uninit();
                let (pre, post) = s.as_bytes().split_at(r.len());
                start[r.start..r.start + pre.len()].copy_from_slice(must_cast_slice(pre));
                gap[0..post.len()].copy_from_slice(must_cast_slice(post));
                // SAFETY: s.len() - r.len() new items have been initialized it is now safe to grow
                // the start slice
                unsafe {
                    self.buf.grow_start(needed_space);
                };
            }
            Ordering::Equal => {
                // SAFETY: we just checked the bounds above
                self.buf
                    .get_slice(r.start..r.end)
                    .expect("we checked the range bounds above, this should never panic")
                    .copy_from_slice(s.as_bytes());
            }
        }
    }

    /// Equivalent of [`String::reserve_exact`] from the standard library
    ///
    /// This will allocate space for the provided value exactly. If inserting multiple string
    /// slices in a loop, use this to reserve enough space in the gap.
    pub fn grow_gap(&mut self, by: usize) {
        self.buf.grow_gap(by);
    }

    /// Shrink the gap
    ///
    /// This is the equivalent of [`String::shrink_to`] from the standard library. The provided
    /// [`Grower`] will handle shrinking by default but this method allows you to shrink the gap
    /// explicitly.
    pub fn shrink_gap(&mut self, by: usize) {
        self.buf.shrink_gap(by);
    }
}

pub struct Drain<'a> {
    chars: Chars<'a>,
    __p: PhantomData<&'a u8>,
}

impl<'a> Deref for Drain<'a> {
    type Target = Chars<'a>;
    fn deref(&self) -> &Self::Target {
        &self.chars
    }
}

impl DerefMut for Drain<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.chars
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;
    use rstest_reuse::apply;

    use crate::grower::test_utils::*;

    use super::GrowingGapString;

    #[apply(grower_template)]
    fn insert(g: TestGrower) {
        let mut s_buf = GrowingGapString::with_grower(g);
        s_buf.insert("Hi", 0);
        assert_eq!(s_buf.get_parts(), ["Hi", ""]);
        s_buf.insert("AA", 1);
        assert_eq!(s_buf.get_parts(), ["HAA", "i"]);
        s_buf.insert("bb", 0);
        assert_eq!(s_buf.get_parts(), ["bb", "HAAi"]);
    }

    #[apply(grower_template)]
    #[should_panic]
    fn insert_panics(g: TestGrower) {
        let mut s_buf = GrowingGapString::with_grower(g);
        s_buf.insert("Hi", 1);
    }

    #[apply(grower_template)]
    fn get(g: TestGrower) {
        let mut s_buf = GrowingGapString::with_grower(g);
        assert!(s_buf
            .get(..)
            .unwrap()
            .map(|s| s.len())
            .into_iter()
            .all(|len| len == 0));
        assert_eq!(s_buf.get(0..5), None);

        s_buf.insert("Hello", 0);
        assert_eq!(s_buf.get(1..3).unwrap(), ["el", ""]);
        assert_eq!(s_buf.get(2..4).unwrap(), ["ll", ""]);
        assert_eq!(s_buf.get(2..5).unwrap(), ["llo", ""]);

        s_buf.insert("Bye", 2);
        assert_eq!(s_buf.get(..).unwrap(), ["HeBye", "llo"]);
        assert_eq!(s_buf.get(1..7).unwrap(), ["eBye", "ll"]);
    }

    #[apply(grower_template)]
    fn get_slice(g: TestGrower) {
        let mut s_buf = GrowingGapString::with_grower(g);
        assert!(s_buf
            .get(..)
            .unwrap()
            .map(|s| s.len())
            .into_iter()
            .all(|len| len == 0));
        assert_eq!(s_buf.get(0..5), None);

        s_buf.insert("Hello", 0);
        assert_eq!(s_buf.get_slice(1..3).unwrap(), "el");
        assert_eq!(s_buf.get_slice(2..4).unwrap(), "ll");
        assert_eq!(s_buf.get_slice(2..5).unwrap(), "llo");

        s_buf.insert("Bye", 2);
        assert_eq!(s_buf.get_slice(..).unwrap(), "HeByello");
        assert_eq!(s_buf.get_slice(1..7).unwrap(), "eByell");
        assert_eq!(s_buf.get_slice(1..9), None);
    }

    #[apply(grower_template)]
    fn drain(g: TestGrower) {
        let mut s_buf = GrowingGapString::with_grower(g);
        s_buf.insert("Hello", 0);
        assert_eq!(s_buf.drain(0..2).as_str(), "He");
        assert_eq!(s_buf.len(), 3);
        assert_eq!(s_buf.drain(0..2).as_str(), "ll");
        assert_eq!(s_buf.len(), 1);
        assert_eq!(s_buf.drain(0..1).as_str(), "o");
        assert!(s_buf.is_empty());

        let mut s_buf = GrowingGapString::with_grower(g);
        s_buf.insert("Hello", 0);
        let dr = s_buf.drain(..);
        assert_eq!(dr.as_str(), "Hello");
        assert!(s_buf.is_empty());
    }

    #[apply(grower_template)]
    fn replace_range(g: TestGrower) {
        let mut s_buf = GrowingGapString::with_grower(g);
        s_buf.insert("Hello", 0);
        s_buf.insert("Bye", 5);

        // same length
        s_buf.replace_range(0..3, "ABC");
        assert_eq!(s_buf.get_slice(..).unwrap(), "ABCloBye");

        // growing
        s_buf.replace_range(5..8, "1234");
        assert_eq!(s_buf.get_slice(..).unwrap(), "ABClo1234");

        // shrinking
        s_buf.replace_range(5..8, "X");
        assert_eq!(s_buf.get_slice(..).unwrap(), "ABCloX4");
    }
}
