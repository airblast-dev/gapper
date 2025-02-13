use core::str;
use std::{
    cmp::Ordering,
    ops::{Range, RangeBounds},
    str::{from_utf8_unchecked, from_utf8_unchecked_mut},
};

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
            // SAFETY: str and [u8] have the same alignment and layout
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
        self.buf.is_empty()
    }

    /// Same as [`str::get`] but for gap buffers
    ///
    /// Returns [`None`] if the range is out of bounds or is not on a char boundary.
    #[inline]
    pub fn get<RB: RangeBounds<usize>>(&self, r: RB) -> Option<[&str; 2]> {
        let r = get_range(self.buf.len(), r)?;
        if !self.is_get_char_boundary(r.start..r.end) {
            return None;
        }

        let [start, end] = self.buf.get_range(r)?;
        unsafe { Some([to_str(start), to_str(end)]) }
    }

    /// Same as [`str::get_mut`] but for gap buffers
    ///
    /// Returns [`None`] if the range is out of bounds or is not on a char boundary.
    #[inline]
    pub fn get_mut<RB: RangeBounds<usize>>(&mut self, r: RB) -> Option<[&mut str; 2]> {
        let r = get_range(self.buf.len(), r)?;
        if !self.is_get_char_boundary(r.start..r.end) {
            return None;
        }

        let [start, end] = self.buf.get_range_mut(r)?;
        unsafe { Some([to_str_mut(start), to_str_mut(end)]) }
    }

    /// Returns a contiguous slice from the gap buffer
    ///
    /// The slice is constructed by shifting the elements to a position that leaves the requested
    /// range as a single slice. This isn't recommended as it will move the gap and can have a
    /// large cost in some cases. Prefer [`GrowingGapString::get`] wherever possible.
    ///
    /// Returns [`None`] if the range is out of bounds or is not on a char boundary.
    #[inline]
    pub fn get_slice<RB: RangeBounds<usize>>(&mut self, r: RB) -> Option<&str> {
        let r = get_range(self.buf.len(), r)?;
        if !self.is_get_char_boundary(r.start..r.end) {
            return None;
        }
        let s = self.buf.get_slice(r)?;
        // SAFETY: we have checked if the range is on a char boundary above
        unsafe { Some(to_str(s)) }
    }

    /// Returns a contiguous slice from the gap buffer
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
        unsafe { Some(to_str_mut(s)) }
    }

    /// Returns both sides of the gap buffer
    #[inline(always)]
    pub fn get_parts(&self) -> [&str; 2] {
        self.buf.get_parts().map(|s| unsafe {
            // SAFETY: we do not allow the gap to be positioned between char boundaries both
            // parts are always valid UTF-8 string slice
            to_str(s)
        })
    }

    /// Returns both sides of the gap buffer as mutable slices
    #[inline(always)]
    pub fn get_parts_mut(&mut self) -> [&mut str; 2] {
        self.buf.get_parts_mut().map(|s| unsafe {
            // SAFETY: we do not allow the gap to be positioned between char boundaries both
            // parts are always valid UTF-8 string slice
            to_str_mut(s)
        })
    }

    /// Checks if the provided range is on a char boundary
    #[inline(always)]
    fn is_get_char_boundary(&self, r: Range<usize>) -> bool {
        let len = self.len();
        matches!(
            r.start.cmp(&len),
            Ordering::Less | Ordering::Equal
            if r.start <= r.end
                && self.buf.get(r.start).is_none_or(|b| u8_is_char_boundary(*b))
                && len >= r.end
                && self.buf.get(r.end).is_none_or(|b| u8_is_char_boundary(*b))
        )
    }

    /// Insert a string at the provided position
    ///
    /// # Panics
    /// If the provided position is greater than [`GrowingGapString::len`] or the position is not
    /// on a char boundary.
    pub fn insert(&mut self, s: &str, at: usize) {
        assert!(
            self.is_get_char_boundary(at..at),
            "insertion should always be on a char boundary"
        );
        // polonius moment
        // can't use [`GrowingGapString::get_parts`] as borrow checker can't infer that the grower
        // field and slices are unrelated in regards to mutability.
        let [start, end] = self.buf.get_parts().map(|s| unsafe {
            // SAFETY: we do not allow the gap to be positioned between char boundaries both
            // parts are always valid UTF-8 string slice
            to_str(s)
        });
        if self.buf.gap_len() < s.len() {
            let new_gap_size = self
                .grower
                .base_gap_size(start, end)
                .min(self.grower.max_gap_size(start, end));
            self.buf.grow_gap(new_gap_size + s.len());
        }
        self.buf.move_gap_start_to(at);

        self.buf.grow_start_with_slice(s.as_bytes());
    }

    /// Equivalent to [`String::drain`] from the standard library
    ///
    /// Returns a string slice to the removed range.
    ///
    /// Shifts the gap's start position to the end of the range, and returns the string slice at
    /// the provided range.
    ///
    /// # Panics
    /// If the provided range is out of bounds or the range start is greater than its end.
    /// If the range does not lie on a char boundary.
    pub fn remove<RB: RangeBounds<usize>>(&mut self, r: RB) -> &str {
        let r = get_range(self.buf.len(), r)
            .expect("range should never be out of bounds when draining");
        assert!(self.is_get_char_boundary(r.start..r.end));

        let [start, end] = self.buf.get_parts().map(|s| unsafe { to_str(s) });

        let max_gap_size = self.grower.max_gap_size(start, end);
        let gap_len = self.gap_len();
        if gap_len > max_gap_size {
            let new_gap_size = self.grower.base_gap_size(start, end).min(max_gap_size);
            self.shrink_gap(gap_len - new_gap_size);
        }

        self.buf.move_gap_start_to(r.end);
        let removed = self.buf.shrink_start_with(r.len());

        unsafe { to_str(removed) }
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
                self.buf.get_parts_mut()[0][r.start..r.start + s.len()]
                    .copy_from_slice(s.as_bytes());
                self.buf.shrink_start(r.len() - s.len());
            }
            Ordering::Less => {
                let needed_space = s.len() - r.len();
                if self.buf.gap_len() < needed_space {
                    let [start, end] = self.buf.get_parts().map(|s| unsafe { to_str(s) });
                    let new_gap_size = self
                        .grower
                        .base_gap_size(start, end)
                        .min(self.grower.max_gap_size(start, end));
                    self.buf.grow_gap(needed_space + new_gap_size);
                }

                self.buf.move_gap_start_to(r.end);
                let start = &mut self.buf.get_parts_mut()[0];
                let (pre, post) = s.as_bytes().split_at(r.len());
                start[r.start..r.start + pre.len()].copy_from_slice(pre);
                self.buf.grow_start_with_slice(post);
            }
            Ordering::Equal => {
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
    ///
    /// # Panics
    /// If the provided value is greater than [`GrowingGapString::gap_len`].
    pub fn shrink_gap(&mut self, by: usize) {
        self.buf.shrink_gap(by);
    }
}

/// [`from_utf8_unchecked`] but panics in debug mode if the bytes are not UTF-8 encoded
#[inline(always)]
unsafe fn to_str(bytes: &[u8]) -> &str {
    debug_assert!(str::from_utf8(bytes).is_ok());
    from_utf8_unchecked(bytes)
}

/// [`from_utf8_unchecked_mut`] but panics in debug mode if the bytes are not UTF-8 encoded
#[inline(always)]
unsafe fn to_str_mut(bytes: &mut [u8]) -> &mut str {
    debug_assert!(str::from_utf8(bytes).is_ok());
    from_utf8_unchecked_mut(bytes)
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
    fn remove(g: TestGrower) {
        let mut s_buf = GrowingGapString::with_grower(g);
        s_buf.insert("Hello", 0);
        assert_eq!(s_buf.remove(0..2), "He");
        assert_eq!(s_buf.len(), 3);
        assert_eq!(s_buf.remove(0..2), "ll");
        assert_eq!(s_buf.len(), 1);
        assert_eq!(s_buf.remove(0..1), "o");
        assert!(s_buf.is_empty());

        let mut s_buf = GrowingGapString::with_grower(g);
        s_buf.insert("Hello", 0);
        let dr = s_buf.remove(..);
        assert_eq!(dr, "Hello");
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
