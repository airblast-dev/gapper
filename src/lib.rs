mod panics;
mod slice;
mod utils;

use core::str;
use std::{
    borrow::Cow,
    fmt::Display,
    ops::{Range, RangeBounds},
};

use panics::{oob_read, position_not_on_char_boundry};
use slice::GapSlice;
use utils::{get_parts_at, start_byte_pos_with_offset, u8_is_char_boundry};

const DEFAULT_GAP_SIZE: usize = 512;

#[derive(Clone, Debug)]
enum GapError {
    OutOfBounds,
    NotCharBoundry,
}

#[derive(Clone, Debug)]
struct GapText {
    buf: Box<[u8]>,
    gap: Range<usize>,
    base_gap_size: usize,
}

impl Default for GapText {
    fn default() -> Self {
        Self {
            buf: Box::new([]),
            gap: 0..0,
            base_gap_size: DEFAULT_GAP_SIZE,
        }
    }
}

impl Display for GapText {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.get(..).unwrap())
    }
}

impl GapText {
    fn new<'a, S>(s: S) -> Self
    where
        S: Into<Cow<'a, str>>,
    {
        let s: Cow<'_, str> = s.into();
        let (buf, gap) = match s {
            Cow::Owned(s) => {
                let mut buf_vec = s.into_bytes();
                let vec_len = buf_vec.len();

                // When an owned string is passed it is likely that it has spare capacity, we can
                // reuse it as a gap buffer.
                let spare = buf_vec.spare_capacity_mut();
                let spare_len = spare.len();

                // SAFETY: MaybeUninit is not copy so it does not benefit from the specialized implementation.
                // In our case we definitely know that the values are not initialized or, are initialized
                // with no drop code.
                // We initialize the values and set the vec length manually for performance.
                unsafe {
                    spare.as_mut_ptr().write_bytes(0, spare.len());
                    buf_vec.set_len(vec_len + spare_len);
                }
                (buf_vec.into_boxed_slice(), vec_len..vec_len + spare_len)
            }

            Cow::Borrowed(s) => (Box::from(s.as_bytes()), 0..0),
        };

        Self {
            buf,
            gap,
            ..Default::default()
        }
    }

    fn with_gap_size<'a, S>(s: S, size: usize) -> Self
    where
        S: Into<Cow<'a, str>>,
    {
        let mut gapstr = Self::new(s);
        gapstr.set_base_gap_size(size);
        gapstr
    }

    fn base_gap_size(&self) -> usize {
        self.base_gap_size
    }

    fn set_base_gap_size(&mut self, gap_size: usize) {
        self.base_gap_size = gap_size;
    }

    /// Move the gap start to the provided position
    ///
    /// # Panics
    /// If the provided position is not on a char boundry, or is out of bounds panics.
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

        if !u8_is_char_boundry(self.buf[start_byte_pos_with_offset(self.gap.clone(), to)]) {
            position_not_on_char_boundry(to);
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
                        (to..self.gap.start, self.gap.end - to - self.gap.start)
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

        #[cold]
        #[inline(never)]
        fn invalid_offset(
            len: usize,
            src_offset: usize,
            dst_offset: usize,
            copy_count: usize,
        ) -> ! {
            panic!(
                "pointers should never overlap when copying, \
                len is {}, source pointer offset is {}, destination \
                pointer offset is {} with a copy count of {}",
                len, src_offset, dst_offset, copy_count
            );
        }

        if self.buf.len() <= src_addr_offset.max(dst_addr_offset) + copy_count
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
    /// # Panics
    ///
    /// Panics if the provided position is greater than the string length ([`GapText::len`]), or
    /// the position does not lie on a char boundry.
    fn insert_gap(&mut self, at: usize) {
        if self.len() < at {
            oob_read();
        }

        if !u8_is_char_boundry(self.buf[start_byte_pos_with_offset(self.gap.clone(), at)]) {
            position_not_on_char_boundry(at);
        }

        let (first, mid, last, before_mid) = if self.base_gap_size() > self.gap.len() {
            let (first, last) = (&self.buf[0..self.gap.start], &self.buf[self.gap.end..]);
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

    fn insert(&mut self, at: usize, s: &str) -> Result<(), GapError> {
        if s.is_empty() {
            return Ok(());
        }

        if at > self.len() {
            return Err(GapError::OutOfBounds);
        } else if !u8_is_char_boundry(self.buf[start_byte_pos_with_offset(self.gap.clone(), at)]) {
            return Err(GapError::NotCharBoundry);
        }

        let gap_len = self.gap.len();
        if gap_len >= s.len() {
            self.move_gap_start_to(at);
            self.spare_capacity_mut()[0..s.len()].copy_from_slice(s.as_bytes());
            self.gap.start += s.len();
            Ok(())
        } else {
            let (first, last) = (&self.buf[0..self.gap.start], &self.buf[self.gap.end..]);
            let (first, mid, last, before_mid) = get_parts_at(first, last, at);
            let (gap_pos, s1, s2) = if before_mid {
                (2, s.as_bytes(), mid)
            } else {
                (3, mid, s.as_bytes())
            };
            self.buf = box_with_gap!(self.base_gap_size(), gap_pos, first, s1, s2, last);
            self.gap.start = at + s.len();
            self.gap.end = self.gap.start + self.base_gap_size();
            Ok(())
        }
    }

    /// Get a string slice from the [`GapText`]
    ///
    /// Returns [`None`] if the provided range is out of bounds or does not lie on a char boundry.
    ///
    /// The provided range may conflict with the gap, in that case a [`GapSlice::Spaced`] variant
    /// is returned containing the requested range with the gap being skipped.
    ///
    /// If a single string slice is strictly required see [`GapText::get_str`].
    #[inline]
    pub fn get<RB: RangeBounds<usize>>(&self, r: RB) -> Option<GapSlice> {
        todo!()
    }

    #[inline(always)]
    fn get_raw<RB: RangeBounds<usize>>(
        buf: &[u8],
        gap: Range<usize>,
        r: RB,
    ) -> Option<(&str, &str)> {
        todo!()
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.buf.len() - self.gap.len()
    }

    /// Returns the gap slice
    #[inline(always)]
    pub fn spare_capacity_mut(&mut self) -> &mut [u8] {
        &mut self.buf[self.gap.start..]
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
        let sample = "Hello, World";
        let mut t = GapText::with_gap_size(sample, gap_size);
        t.insert_gap(0);
        t.insert(3, "AAAAA")?;
        assert_eq!(&t.buf[..3], b"Hel");
        assert_eq!(&t.buf[3..t.gap.start], "AAAAA".as_bytes());
        assert_eq!(&t.buf[t.gap.end..], "lo, World".as_bytes());

        Ok(())
    }

    #[rstest]
    #[case::empty_gap(0)]
    #[case::insertion_exceeds_gap(1)]
    #[case::insertion_fits_in_gap(5)]
    #[case::very_large_gap(1024)]
    fn insert_before_gap(#[case] gap_size: usize) -> Result<(), GapError> {
        let sample = "Hello, World";
        let mut t = GapText::with_gap_size(sample, gap_size);
        t.insert_gap(6);
        t.insert(3, "AAAAA")?;
        dbg!(&t.buf);
        assert_eq!(&t.buf[..3], b"Hel");
        assert_eq!(&t.buf[3..t.gap.start], "AAAAA".as_bytes());
        assert_eq!(&t.buf[t.gap.end..], "lo, World".as_bytes());

        Ok(())
    }
}
