mod slice;
mod utils;

use core::str;
use std::{
    borrow::Cow,
    fmt::Display,
    mem::MaybeUninit,
    ops::{Bound, Range, RangeBounds},
};

use slice::GapSlice;
use utils::{box_with_gap, end_byte_pos_with_offset, get_range, is_get_single, u8_is_char_boundry};

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
    pub fn move_gap_start_to(&mut self, to: usize) {
        if self.gap.start == to {
            return;
        }
        if self.gap.is_empty() {
            self.gap.start = to;
            self.gap.end = to;
            return;
        }

        if self.buf.len() - self.gap.len() < to {
            #[cold]
            #[inline(never)]
            #[track_caller]
            fn oob_read() -> ! {
                panic!("index for gap move is out of bounds");
            }
            oob_read();
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
                    // cant take any shortcuts use fallback
                    //
                    // this probably could be slightly more optimized since we dont actually have to
                    // move the gap, we just need to copy the values from the position that the gap
                    // range will be set to
                    if self.gap.start > to {
                        self.buf[to..self.gap.end].rotate_right(self.gap.len());
                        unsafe { self.shift_gap_left(self.gap.start - to) };
                    } else {
                        self.buf[self.gap.start..to + self.gap.len()].rotate_left(self.gap.len());
                        unsafe { self.shift_gap_right(to - self.gap.start) };
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
    /// Panics if the provided position is greater than the string length ([`GapText::len`]).
    fn insert_gap(&mut self, at: usize) {
        let (first, mid, last) = if self.gap.is_empty() {
            (&self.buf[..at], [].as_slice(), &self.buf[at..])
        } else if self.base_gap_size() > self.gap.len() {
            let (mut first, mut last) = (&self.buf[0..self.gap.start], &self.buf[self.gap.end..]);
            let mid = if first.len() > at {
                let (f, mid) = first.split_at(at);
                first = f;
                mid
            } else {
                let (mid, l) = last.split_at(at - first.len());
                last = l;
                mid
            };
            (first, mid, last)
        } else {
            self.move_gap_start_to(at);
            return;
        };

        self.buf = box_with_gap!(self.base_gap_size(), 2, first, mid, last);
        self.gap.start = at;
        self.gap.end = at + self.base_gap_size();
    }

    fn insert(&mut self, at: usize, s: &str) -> Result<(), GapError> {
        if s.is_empty() {
            return Ok(());
        }

        let gap_len = self.gap.len();
        if gap_len > 0 && !u8_is_char_boundry(self.buf[self.gap.start]) {
            Err(GapError::NotCharBoundry)
        } else if gap_len >= s.len() {
            self.move_gap_start_to(at);
            self.spare_capacity_mut()[0..s.len()].copy_from_slice(s.as_bytes());
            self.gap.start += s.len();
            Ok(())
        } else {
            todo!()
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

    use super::GapText;
    #[fixture]
    #[once]
    fn large_str() -> String {
        String::from_utf8((1..128).collect()).unwrap().repeat(10)
    }

    #[rstest]
    fn move_gap_start(large_str: &str) -> Result<(), GapError> {
        let sample = large_str;
        let mut t = GapText::new(large_str);
        dbg!(&t.gap);
        t.insert_gap(64);
        dbg!(&t.gap);
        dbg!(&t.buf.len());
        for gs in 0..1270 {
            t.move_gap_start_to(gs);
            t.buf[t.gap.clone()].copy_from_slice([0; DEFAULT_GAP_SIZE].as_slice());
            assert_eq!(&t.buf[..t.gap.start], sample[..gs].as_bytes());
            assert_eq!(&t.buf[t.gap.end..], sample[gs..].as_bytes());
        }
        dbg!("Asdasdas");
        for gs in (0..1270).rev() {
            dbg!(&t.gap);
            t.move_gap_start_to(gs);
            dbg!(&t.gap);
            t.buf[t.gap.clone()].copy_from_slice([0; DEFAULT_GAP_SIZE].as_slice());
            assert_eq!(&t.buf[..t.gap.start], sample[..gs].as_bytes());
            assert_eq!(&t.buf[t.gap.end..], sample[gs..].as_bytes());
        }

        // Test case where the move difference is larger than the gap size.
        t.move_gap_start_to(0);
        t.buf[t.gap.clone()].fill(0);
        assert_eq!(&t.buf[DEFAULT_GAP_SIZE..], sample.as_bytes());
        t.move_gap_start_to(1200);
        t.buf[t.gap.clone()].fill(0);
        assert_eq!(&t.buf[..1200], sample[..1200].as_bytes());
        t.move_gap_start_to(0);
        t.buf[t.gap.clone()].fill(0);
        assert_eq!(&t.buf[..t.gap.start], sample[..t.gap.start].as_bytes());
        assert_eq!(&t.buf[DEFAULT_GAP_SIZE..], sample.as_bytes());

        Ok(())
    }
}
