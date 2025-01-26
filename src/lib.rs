pub mod builder;
mod panics;
mod slice;
mod utils;

use core::str;
use core::str::from_utf8_unchecked;
use std::{
    borrow::Cow,
    fmt::Display,
    ops::{Range, RangeBounds},
};

use builder::{GapBufBuilder, MaxGapSize};
use panics::{invalid_offset, oob_read, position_not_on_char_boundary};
use slice::GapSlice;
use utils::{
    end_byte_pos_with_offset, get_parts_at, get_range, is_get_single, start_byte_pos_with_offset,
    u8_is_char_boundary,
};

const DEFAULT_GAP_SIZE: usize = 512;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GapError {
    OutOfBounds,
    NotCharBoundary,
}

#[derive(Clone, Debug)]
pub struct GapText {
    buf: Box<[u8]>,
    gap: Range<usize>,
    base_gap_size: usize,
    max_gap_size: MaxGapSize,
}

impl Default for GapText {
    fn default() -> Self {
        Self {
            buf: Box::new([]),
            gap: 0..0,
            base_gap_size: DEFAULT_GAP_SIZE,
            max_gap_size: MaxGapSize::default(),
        }
    }
}

impl Display for GapText {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (s1, s2) = self.get_str_slices();
        write!(f, "{s1}{s2}")
    }
}

impl GapText {
    pub fn new<'a, S>(s: S) -> Self
    where
        S: Into<Cow<'a, str>>,
    {
        GapBufBuilder::new().build(s)
    }

    pub fn with_gap_size<'a, S>(s: S, size: usize) -> Self
    where
        S: Into<Cow<'a, str>>,
    {
        let s: Cow<'_, str> = s.into();
        GapBufBuilder::new().base_gap_size(size).build(s)
    }

    #[inline]
    pub fn base_gap_size(&self) -> usize {
        self.base_gap_size
    }

    #[inline]
    pub fn set_base_gap_size(&mut self, gap_size: usize) {
        self.base_gap_size = gap_size;
    }

    /// Move the gap start to the provided position
    ///
    /// # Panics
    /// If the provided position is not on a char boundary, or is out of bounds panics.
    pub fn move_gap_start_to(&mut self, to: usize) {
        if self.gap.start == to {
            return;
        }
        if self.gap.is_empty() {
            self.gap.start = to;
            self.gap.end = to;
            return;
        }

        if self.len() < to {
            oob_read();
        }

        if !self.is_char_boundary(to) {
            position_not_on_char_boundary(to);
        }

        enum SurroundsDirection {
            Right(usize),
            Left(usize),
            False,
        }

        #[inline(always)]
        fn surrounds_gap_range(gap: &Range<usize>, pos: usize) -> SurroundsDirection {
            if gap.start < pos
                && gap.end.saturating_add(gap.len()) > pos
                && pos - gap.start <= gap.len()
            {
                SurroundsDirection::Right(pos - gap.start)
            } else if pos < gap.start
                && gap.start.saturating_sub(gap.len()) <= pos
                && gap.start - pos <= gap.len()
            {
                SurroundsDirection::Left(gap.start - pos)
            } else {
                SurroundsDirection::False
            }
        }

        let mut left_shift = 0;
        let mut right_shift = 0;

        let (src_addr_offset, dst_addr_offset, copy_count): (usize, usize, usize) =
            match surrounds_gap_range(&self.gap, to) {
                SurroundsDirection::Right(r) => {
                    let copy_count = r;
                    right_shift = r;
                    (self.gap.end, self.gap.start, copy_count)
                }
                SurroundsDirection::Left(l) => {
                    let copy_count = l;
                    left_shift = l;
                    (to, self.gap.end - copy_count, copy_count)
                }
                SurroundsDirection::False => {
                    // cant panic
                    // SurroundsDirection::False is only returned
                    // if to + gap.start < gap.end
                    // or gap.end < to
                    let (src, dst) = if self.gap.start > to {
                        left_shift = self.gap.start - to;
                        (to..self.gap.start, self.gap.end - left_shift)
                    } else {
                        right_shift = to - self.gap.start;
                        (self.gap.end..to + self.gap.len(), self.gap.start)
                    };

                    self.buf.copy_within(src, dst);
                    unsafe {
                        self.shift_gap_right(right_shift);
                        self.shift_gap_left(left_shift);
                    }
                    return;
                }
            };

        if self.buf.len() < src_addr_offset.max(dst_addr_offset) + copy_count
            || src_addr_offset.abs_diff(dst_addr_offset) < copy_count
        {
            // this should never run, in case a bug is present above this avoids undefined behavior
            invalid_offset(self.buf.len(), src_addr_offset, dst_addr_offset, copy_count);
        }

        // we do not strictly have to use unsafe to accomplish this
        // it does remove a bunch of boiler plate code as otherwise we have to do a bunch of
        // panicy operations in the conditions above.
        //
        // Instead we do a few checks and do a fast copy.

        let ptr = self.buf.as_mut_ptr();
        unsafe {
            let src = ptr.add(src_addr_offset);
            let dst = ptr.add(dst_addr_offset);
            std::ptr::copy_nonoverlapping(src, dst, copy_count);
        }

        debug_assert_ne!(right_shift == 0, left_shift == 0);
        unsafe {
            self.shift_gap_right(right_shift);
            self.shift_gap_left(left_shift);
        }
    }

    /// Shifts the gap right by N
    ///
    /// # Safety
    ///
    /// If the values exposed on the left side end up creating a non UTF-8 this can cause UB or
    /// panics in some code paths.
    ///
    /// Generally before calling this function the bytes on the right should be copied to the left.
    #[inline(always)]
    unsafe fn shift_gap_right(&mut self, by: usize) {
        self.gap.start += by;
        self.gap.end += by;
    }

    /// Shifts the gap left by N
    ///
    /// # Safety
    ///
    /// If the values exposed on the right side end up creating a non UTF-8 this can cause UB or
    /// panics in some code paths.
    ///
    /// Generally before calling this function the bytes on the left should be copied to the right.
    #[inline(always)]
    unsafe fn shift_gap_left(&mut self, by: usize) {
        self.gap.start -= by;
        self.gap.end -= by;
    }

    /// Insert a gap at a specific position
    ///
    /// If a gap already exists, and is bigger than the base_gap_size, the gap start will be moved
    /// to the provided position.
    ///
    /// # Panics
    ///
    /// Panics if the provided position is greater than the string length ([`GapText::len`]), or
    /// the position does not lie on a char boundary.
    pub fn insert_gap(&mut self, at: usize) {
        if self.len() < at {
            oob_read();
        }

        if !self.is_char_boundary(at) {
            position_not_on_char_boundary(at);
        }

        let (first, mid, last, before_mid) = if self.base_gap_size() > self.gap.len() {
            let (first, last) = self.get_slices();
            get_parts_at(first, last, at)
        } else {
            self.move_gap_start_to(at);
            return;
        };

        self.buf = box_with_gap!(
            self.base_gap_size(),
            if before_mid { 1 } else { 2 },
            first,
            mid,
            last
        );
        self.gap.start = at;
        self.gap.end = at + self.base_gap_size();
    }

    /// Inserts the provided string at the provided index
    ///
    /// Returns an error if the provided range is not on a char boundary, or is out of bounds.
    pub fn insert(&mut self, at: usize, s: &str) -> Result<(), GapError> {
        if s.is_empty() {
            return Ok(());
        }

        if at > self.len() {
            return Err(GapError::OutOfBounds);
        } else if !self.is_char_boundary(at) {
            return Err(GapError::NotCharBoundary);
        }

        let gap_len = self.gap.len();
        if gap_len >= s.len() {
            self.move_gap_start_to(at);
            self.spare_capacity_mut()[0..s.len()].copy_from_slice(s.as_bytes());
            self.gap.start += s.len();
        } else {
            let (first, last) = self.get_slices();
            let (first, mid, last, before_mid) = get_parts_at(first, last, at);
            let (gap_pos, s1, s2) = if before_mid {
                (2, s.as_bytes(), mid)
            } else {
                (3, mid, s.as_bytes())
            };
            self.buf = box_with_gap!(self.base_gap_size(), gap_pos, first, s1, s2, last);
            self.gap.start = at + s.len();
            self.gap.end = self.gap.start + self.base_gap_size();
        }

        Ok(())
    }

    /// Get a string slice from the [`GapText`]
    ///
    /// Returns [`None`] if the provided range is out of bounds or does not lie on a char boundary.
    #[inline]
    pub fn get<RB: RangeBounds<usize>>(&self, r: RB) -> Option<GapSlice> {
        let r = get_range(self.len(), r)?;
        if !self.is_char_boundary(r.start) || !self.is_char_boundary(r.end) {
            return None;
        }

        let start = start_byte_pos_with_offset(self.gap.clone(), r.start);
        let end = end_byte_pos_with_offset(self.gap.clone(), r.end);
        if is_get_single(self.gap.start, start, end) {
            return Some(unsafe { GapSlice(from_utf8_unchecked(&self.buf[start..end]), "") });
        }
        let (first, last) = self.get_slices();
        unsafe {
            Some(GapSlice(
                from_utf8_unchecked(&first[start..]),
                from_utf8_unchecked(&last[..end - self.gap.end]),
            ))
        }
    }

    /// Returns the string slice for the provided range
    ///
    /// Returns [`None`] if the provided range is out of bounds or does not lie on a char boundary.
    ///
    /// # Note
    /// This may cause the gap to be moved, as such it is only recommended if you know the provided
    /// range will be small.
    #[inline(always)]
    pub fn get_str<RB: RangeBounds<usize>>(&mut self, r: RB) -> Option<&str> {
        let r = get_range(self.len(), r)?;
        if !self.is_char_boundary(r.start) || !self.is_char_boundary(r.end) {
            return None;
        }

        self.move_gap_start_to(r.end);
        unsafe { Some(from_utf8_unchecked(&self.buf[r.start..r.end])) }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.buf.len() - self.gap.len()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the gap slice
    ///
    /// The returned slice may contain zeros, or content that were here before the gap was moved.
    #[inline(always)]
    pub fn spare_capacity_mut(&mut self) -> &mut [u8] {
        &mut self.buf[self.gap.start..self.gap.end]
    }

    /// Grows the gap by the provided value
    ///
    /// When inserting multiple slices, the gap may be resized multiple times possibly causing large copies.
    /// To avoid this, you can grow the gap to account for all of the slices and insert them via
    /// [`GapText::insert`].
    ///
    /// # Example
    ///
    /// Good
    /// ```
    /// use gapstr::GapText;
    ///
    /// // A gap with a size of 3 defeats the purpose of a gap buffer, only used here to emulate
    /// // the worst case.
    /// let mut gap_str = GapText::with_gap_size("New GapText!", 3);
    /// let slices = vec!["Hello, World!"; 10];
    /// let len = slices.iter().copied().map(str::len).sum();
    ///
    /// // Reallocates the buffer once.
    /// gap_str.grow(len);
    ///
    /// // Copy over the slices without reallocating.
    /// for s in slices {
    ///     gap_str.insert(5, s);
    /// }
    /// ```
    ///
    /// Bad
    /// ```
    /// use gapstr::GapText;
    ///
    /// // A gap with a size of 3 defeats the purpose of a gap buffer, only used here to emulate
    /// // the worst case.
    /// let mut gap_str = GapText::with_gap_size("New GapText!", 3);
    /// let slices = vec!["Hello, World!"; 10];
    ///
    /// // Since our gap is smaller than the inserted slices length, this reallocates the internal
    /// // buffer on every loop.
    /// for s in slices {
    ///     gap_str.insert(5, s);
    /// }
    /// ```
    pub fn grow(&mut self, by: usize) {
        let (start, end) = self.get_slices();
        let gap_len = self.gap.len();
        self.buf = box_with_gap!(gap_len + by, 1, start, end);
        self.gap.end += by;
    }

    pub fn shrink_to(&mut self, to: usize) {
        if self.gap.len() < to {
            return;
        }

        let (first, last) = self.get_slices();
        self.buf = box_with_gap!(to, 1, first, last);
    }

    /// Returns the the parts before and after the gap
    #[inline(always)]
    fn get_slices(&self) -> (&[u8], &[u8]) {
        unsafe {
            (
                self.buf.get_unchecked(0..self.gap.start),
                self.buf.get_unchecked(self.gap.end..),
            )
        }
    }

    /// Returns the the parts before and after the gap as a string slice
    #[inline(always)]
    fn get_str_slices(&self) -> (&str, &str) {
        let (s1, s2) = self.get_slices();
        // SAFETY: left and right side of the gap is always guaranteed to be valid UTF-8
        unsafe { (from_utf8_unchecked(s1), from_utf8_unchecked(s2)) }
    }

    #[inline(always)]
    fn is_char_boundary(&self, pos: usize) -> bool {
        if pos == 0 {
            return true;
        }
        let real_pos = start_byte_pos_with_offset(self.gap.clone(), pos);
        match self.buf.get(real_pos) {
            None => real_pos == self.buf.len(),
            Some(u) => u8_is_char_boundary(*u),
        }
    }
}

#[cfg(test)]
mod tests {

    use rstest::{fixture, rstest};

    use crate::{GapError, DEFAULT_GAP_SIZE};

    // this is very useless where do not know the exact size of the gap
    // copying this instead of using fill, or similar methods perform much better when testing with miri
    // without this some of the tests take near a minute to complete
    const DEFAULT_ZEROS: [u8; DEFAULT_GAP_SIZE] = [0; DEFAULT_GAP_SIZE];

    use super::GapText;
    #[fixture]
    #[once]
    fn large_str() -> String {
        String::from_utf8((1..128).collect()).unwrap().repeat(10)
    }

    // the idea is to fill our string with non zero bytes, and fill the gap with zero's
    // if any zero is leaked outside of the gap, the test fails
    // (we actually don't check if a null byte leaks, but rather compare it to the source string
    // that doesn't contain null bytes)
    #[rstest]
    fn move_gap_start(large_str: &str) -> Result<(), GapError> {
        let sample = large_str;
        let mut t = GapText::new(large_str);
        t.insert_gap(64);
        for gs in 0..1270 {
            t.move_gap_start_to(gs);
            t.buf[t.gap.clone()].copy_from_slice(&DEFAULT_ZEROS);
            assert_eq!(&t.buf[..t.gap.start], sample[..gs].as_bytes());
            assert_eq!(&t.buf[t.gap.end..], sample[gs..].as_bytes());
        }
        for gs in (0..1270).rev() {
            t.move_gap_start_to(gs);
            t.buf[t.gap.clone()].copy_from_slice(&DEFAULT_ZEROS);
            assert_eq!(&t.buf[..t.gap.start], sample[..gs].as_bytes());
            assert_eq!(&t.buf[t.gap.end..], sample[gs..].as_bytes());
        }

        // Test case where the move difference is larger than the gap size.
        t.move_gap_start_to(0);
        t.buf[t.gap.clone()].copy_from_slice(&DEFAULT_ZEROS);
        assert_eq!(&t.buf[DEFAULT_GAP_SIZE..], sample.as_bytes());
        t.move_gap_start_to(1200);
        t.buf[t.gap.clone()].copy_from_slice(&DEFAULT_ZEROS);
        assert_eq!(&t.buf[..1200], sample[..1200].as_bytes());
        t.move_gap_start_to(0);
        t.buf[t.gap.clone()].copy_from_slice(&DEFAULT_ZEROS);
        assert_eq!(&t.buf[..t.gap.start], sample[..t.gap.start].as_bytes());
        assert_eq!(&t.buf[DEFAULT_GAP_SIZE..], sample.as_bytes());

        Ok(())
    }

    #[rstest]
    #[case::empty_gap(0)]
    #[case::insertion_exceeds_gap(1)]
    #[case::insertion_fits_in_gap(5)]
    #[case::very_large_gap(1024)]
    fn insert_after_gap(#[case] gap_size: usize) -> Result<(), GapError> {
        let sample = "Hello, Worlぬ";
        let mut t = GapText::with_gap_size(sample, gap_size);
        t.insert_gap(0);
        t.insert(3, "AAぢAA")?;
        assert_eq!(&t.buf[..3], b"Hel");
        assert_eq!(&t.buf[3..t.gap.start], "AAぢAA".as_bytes());
        assert_eq!(&t.buf[t.gap.end..], "lo, Worlぬ".as_bytes());

        Ok(())
    }

    #[rstest]
    #[case::empty_gap(0)]
    #[case::insertion_exceeds_gap(1)]
    #[case::insertion_fits_in_gap(5)]
    #[case::very_large_gap(1024)]
    fn insert_before_gap(#[case] gap_size: usize) -> Result<(), GapError> {
        let sample = "Hello, Worlぬ";
        let mut t = GapText::with_gap_size(sample, gap_size);
        t.insert_gap(6);
        t.insert(3, "AAぢAA")?;
        assert_eq!(&t.buf[..3], b"Hel");
        assert_eq!(&t.buf[3..t.gap.start], "AAぢAA".as_bytes());
        assert_eq!(&t.buf[t.gap.end..], "lo, Worlぬ".as_bytes());

        Ok(())
    }

    #[test]
    fn insert_bad_pos() -> Result<(), GapError> {
        let sample = "Hello, Worlぬ";
        let mut t = GapText::with_gap_size(sample, 20);
        t.insert_gap(6);
        //assert_eq!(t.insert(11, "AAぢAA"), Ok(()));
        assert_eq!(t.insert(12, "AAぢAA"), Err(GapError::NotCharBoundary));
        assert_eq!(t.insert(13, "AAぢAA"), Err(GapError::NotCharBoundary));
        //assert_eq!(t.insert(14, "AAぢAA"), Ok(()));
        assert_eq!(t.insert(15, "AAぢAA"), Err(GapError::OutOfBounds));
        assert_eq!(t.insert(16, "AAぢAA"), Err(GapError::OutOfBounds));
        Ok(())
    }

    #[rstest]
    #[case::empty_gap(0)]
    #[case::small_gap(1)]
    #[case::small_gap(2)]
    #[case::small_gap(3)]
    #[case::medium_gap(128)]
    #[case::large(512)]
    fn get(#[case] gap_size: usize) {
        let sample = "Hello, World";
        let mut t = GapText::with_gap_size(sample.to_string(), gap_size);
        t.insert_gap(2);

        let s = t.get(0..4).unwrap();
        assert_eq!(s, "Hell");
        let s = t.get(0..2).unwrap();
        assert_eq!(s, "He");
        let s = t.get(2..5).unwrap();
        assert_eq!(s, "llo");
        let s = t.get(3..9).unwrap();
        assert_eq!(s, "lo, Wo");
        let s = t.get(9..).unwrap();
        assert_eq!(s, "rld");
        let s = t.get(..).unwrap();
        assert_eq!(s, "Hello, World");
        let s = t.get(..12).unwrap();
        assert_eq!(s, "Hello, World");
        assert!(t.get(..15).is_none());
        assert!(t.get(25..).is_none());
        assert!(t.get(0..13).is_none());
        assert!(t.get(3..14).is_none());
    }

    #[rstest]
    #[case::empty_gap(0)]
    #[case::small_gap(1)]
    #[case::small_gap(2)]
    #[case::small_gap(3)]
    #[case::medium_gap(128)]
    #[case::large(512)]
    fn get_str(#[case] gap_size: usize) {
        let sample = "Hello, World";
        let mut t = GapText::with_gap_size(sample.to_string(), gap_size);
        t.insert_gap(2);

        let s = t.get_str(0..4).unwrap();
        assert_eq!(s, "Hell");
        let s = t.get_str(0..2).unwrap();
        assert_eq!(s, "He");
        let s = t.get_str(2..5).unwrap();
        assert_eq!(s, "llo");
        let s = t.get_str(3..9).unwrap();
        assert_eq!(s, "lo, Wo");
        let s = t.get_str(9..).unwrap();
        assert_eq!(s, "rld");
        let s = t.get_str(..).unwrap();
        assert_eq!(s, "Hello, World");
        let s = t.get_str(..12).unwrap();
        assert_eq!(s, "Hello, World");
        assert!(t.get_str(..15).is_none());
        assert!(t.get_str(25..).is_none());
        assert!(t.get_str(0..13).is_none());
        assert!(t.get_str(3..14).is_none());
    }
}
