mod slice;
mod utils;

use core::str;
use std::ops::{Bound, Range, RangeBounds};

use slice::GapSlice;
use utils::u8_is_char_boundry;

const DEFAULT_GAP_SIZE: usize = 512;

#[derive(Clone, Debug)]
enum GapError {
    OutOfBounds { len: usize, target: usize },
    NotCharBoundry,
}

#[derive(Clone, Debug)]
struct GapText {
    buf: Vec<u8>,
    gap: Range<usize>,
    base_gap_size: usize,
}

impl GapText {
    fn new(s: String) -> Self {
        Self {
            buf: s.into_bytes(),
            gap: 0..0,
            base_gap_size: DEFAULT_GAP_SIZE,
        }
    }

    fn with_gap_size(s: String, size: usize) -> Self {
        Self {
            buf: s.into_bytes(),
            gap: 0..0,
            base_gap_size: size,
        }
    }

    fn base_gap_size(&self) -> usize {
        self.base_gap_size
    }

    fn set_base_gap_size(&mut self, gap_size: usize) {
        self.base_gap_size = gap_size;
    }

    fn insert(&mut self, at: usize, s: &str) -> Result<(), GapError> {
        self.move_gap_start_to(at)?;
        if !u8_is_char_boundry(*self.buf.get(at).ok_or(GapError::OutOfBounds {
            len: self.buf.len() - self.gap.len(),
            target: at,
        })?) {
            return Err(GapError::NotCharBoundry);
        };
        // ideal case, the gap has enough space
        if s.len() <= self.gap.len() {
            self.buf[self.gap.start..self.gap.start + s.len()].copy_from_slice(s.as_bytes());
            self.gap.start += s.len();
        } else {
            // Since we are already shifting a possibly large number of elements, we should also
            // add a gap. This results in only 2 likely small copies and one possibly large copy.
            self.buf[self.gap.clone()].copy_from_slice(&s.as_bytes()[..self.gap.len()]);

            // the number of elements that were inserted into the existing gap.
            let inserted = self.gap.len();

            // since the insertion must exceed the gap length to reach this path, and we fill the
            // existing gap before copying the overflow, the start and end must be zero at this
            // stage.
            self.gap.start = self.gap.end;

            self.buf.reserve(s.len() + self.base_gap_size);

            self.buf.extend_from_slice(&s.as_bytes()[inserted..]);
            self.insert_gap(self.buf.len());

            self.buf[at + inserted..].rotate_right(s.len() - inserted + self.gap.len());

            // after the string is inserted the gap must always be after the inserted bytes
            // the rotate performed above ensures that
            self.gap.start = at + s.len();
            self.gap.end = self.gap.start + self.base_gap_size;
        }

        Ok(())
    }

    fn delete(&mut self, Range { start, end }: Range<usize>) -> Result<(), GapError> {
        // we dont actually have to delete anything, so we move the gap to the end of the range and
        // then mark the "deleted" range as part of the gap.
        self.move_gap_start_to(end)?;
        assert_eq!(self.gap.start, end);
        self.gap.start -= end - start;
        Ok(())
    }

    fn replace(&mut self, Range { start, end }: Range<usize>, s: &str) -> Result<(), GapError> {
        let to = (end - start).max(s.len());
        self.move_gap_start_to(start + to)?;
        self.gap.start -= (end - start).saturating_sub(s.len());
        if self.gap.len() + s.len().saturating_sub(end - start) <= self.gap.len() {
            self.buf[start..start + s.len()].copy_from_slice(s.as_bytes());
            self.gap.start += s.len().saturating_sub(end - start);
        } else {
            self.buf[start..self.gap.end].copy_from_slice(&s.as_bytes()[..self.gap.end - start]);
            self.buf
                .extend_from_slice(&s.as_bytes()[self.gap.end - start..]);
            self.buf.extend_from_slice(&[0; DEFAULT_GAP_SIZE]);
            self.buf
                .rotate_right(s.len() - (self.gap.end - start) + DEFAULT_GAP_SIZE);
            self.gap.start = start + s.len();
            self.gap.end = self.gap.start + DEFAULT_GAP_SIZE;
        }

        Ok(())
    }

    pub fn move_gap_start_to(&mut self, to: usize) -> Result<(), GapError> {
        if self.gap.start == to {
            return Ok(());
        }
        if self.gap.is_empty() {
            self.gap.start = to;
            self.gap.end = to;
            return Ok(());
        }

        if self.buf.len() - self.gap.len() < to {
            return Err(GapError::OutOfBounds {
                len: self.buf.len() - self.gap.len(),
                target: to,
            });
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
                        self.shift_gap_left(self.gap.start - to);
                    } else {
                        self.buf[self.gap.start..to + self.gap.len()].rotate_left(self.gap.len());
                        self.shift_gap_right(to - self.gap.start);
                    }

                    return Ok(());
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
        unsafe {
            std::ptr::copy_nonoverlapping(
                self.buf.as_ptr().add(src_addr_offset),
                self.buf.as_mut_ptr().add(dst_addr_offset),
                copy_count,
            );
        }

        debug_assert_ne!(right_shift == 0, left_shift == 0);

        self.shift_gap_right(right_shift);
        self.shift_gap_left(left_shift);

        Ok(())
    }

    #[inline(always)]
    fn shift_gap_right(&mut self, by: usize) {
        self.gap.start += by;
        self.gap.end += by;
    }

    #[inline(always)]
    fn shift_gap_left(&mut self, by: usize) {
        self.gap.start -= by;
        self.gap.end -= by;
    }

    fn insert_gap(&mut self, at: usize) {
        assert_eq!(self.gap.start, self.gap.end);
        self.buf
            .extend(std::iter::repeat(0).take(self.base_gap_size));
        self.buf[at..].rotate_right(self.base_gap_size);
        self.gap.start = at;
        self.gap.end = at + self.base_gap_size;
    }

    #[inline(always)]
    fn start_byte_pos_with_offset(gap: Range<usize>, byte_pos: usize) -> usize {
        if gap.start > byte_pos {
            byte_pos
        } else {
            gap.len() + byte_pos
        }
    }

    #[inline(always)]
    fn end_byte_pos_with_offset(gap: Range<usize>, byte_pos: usize) -> usize {
        if gap.start >= byte_pos {
            byte_pos
        } else {
            gap.len() + byte_pos
        }
    }

    #[inline]
    pub fn get<RB: RangeBounds<usize>>(&self, r: RB) -> Option<GapSlice> {
        Self::get_raw(&self.buf, self.gap.clone(), r)
    }

    #[inline]
    pub fn get_str<RB: RangeBounds<usize>>(&mut self, r: RB) -> Option<&str> {
        let r = get_range(self.buf.len() - self.gap.len(), r);
        let read_len = r.len();

        let buf = self.buf.as_ptr();
        if let GapSlice::Single(s) = Self::get_raw(
            unsafe { core::slice::from_raw_parts(buf, self.buf.len()) },
            self.gap.clone(),
            r.clone(),
        )? {
            return Some(s);
        }

        let gap_len = self.gap.len();
        let spare_len = self.buf.capacity() - self.buf.len();
        let buf = if gap_len > read_len {
            &mut self.buf[self.gap.start..self.gap.start + read_len]
        } else if spare_len > read_len {
            unsafe {
                core::slice::from_raw_parts_mut(
                    self.buf.spare_capacity_mut().as_mut_ptr() as *mut u8,
                    read_len,
                )
            }
        } else {
            self.buf.reserve(read_len);

            unsafe {
                core::slice::from_raw_parts_mut(
                    self.buf.spare_capacity_mut().as_mut_ptr() as *mut u8,
                    read_len,
                )
            }
        };

        let buf_ptr = buf.as_mut_ptr();

        let GapSlice::Spaced(s1, s2) = self.get(r)? else {
            unreachable!()
        };

        unsafe {
            buf_ptr.copy_from_nonoverlapping(s1.as_ptr(), s1.len());
            buf_ptr
                .add(s1.len())
                .copy_from_nonoverlapping(s2.as_ptr(), s2.len());

            Some(str::from_utf8_unchecked(core::slice::from_raw_parts(
                buf_ptr, read_len,
            )))
        }
    }

    #[inline(always)]
    fn get_raw<RB: RangeBounds<usize>>(
        buf: &[u8],
        gap: Range<usize>,
        r: RB,
    ) -> Option<GapSlice<'_>> {
        let s_len = buf.len() - gap.len();

        let Range { start, end } = get_range(s_len, r);

        // check the range values
        if start > end || s_len < end {
            return None;
        }

        let start_with_offset = Self::start_byte_pos_with_offset(gap.clone(), start);
        let end_with_offset = Self::end_byte_pos_with_offset(gap.clone(), end);

        debug_assert!(start_with_offset <= end_with_offset);

        // perform char boundry check
        if !is_get_char_boundry(buf, buf[start_with_offset], end_with_offset) {
            return None;
        }

        // handles all of the single piece conditions
        // Range before gap case, Range after gap case, and start in gap case
        //
        // after this check
        // - start_with_offset == start
        // - start < self.gap.start
        // - self.gap.start < end
        if is_get_single(gap.start, start, end) {
            return Some(GapSlice::Single(unsafe {
                str::from_utf8_unchecked(&buf[start_with_offset..end_with_offset])
            }));
        }

        debug_assert_eq!(start_with_offset, start);

        // when the base gap value is 0 the end and end_with_offset maybe equal since a gap is not
        // inserted yet
        debug_assert!(end != end_with_offset || gap.is_empty());

        unsafe {
            let first = str::from_utf8_unchecked(&buf[start_with_offset..gap.start]);
            let second = str::from_utf8_unchecked(&buf[gap.end..end_with_offset]);

            Some(GapSlice::Spaced(first, second))
        }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.buf.len() - self.gap.len()
    }
}

#[inline]
fn get_range<RB: RangeBounds<usize>>(max: usize, r: RB) -> Range<usize> {
    let start = match r.start_bound() {
        Bound::Unbounded => 0,
        Bound::Excluded(i) => i.saturating_add(1),
        Bound::Included(i) => *i,
    };
    let end = match r.end_bound() {
        Bound::Unbounded => max,
        Bound::Excluded(i) => *i,
        Bound::Included(i) => i.saturating_add(1),
    };

    start..end
}

#[inline(always)]
fn is_get_single(gap_start: usize, start: usize, end: usize) -> bool {
    end <= gap_start || gap_start <= start
}

#[inline]
fn is_get_char_boundry(buf: &[u8], b1: u8, end_index: usize) -> bool {
    u8_is_char_boundry(b1)
            // NOTE: Option::is_none_or is more elegant but requires higher MSRV
            && buf
                .get(end_index)
                .filter(|b| !u8_is_char_boundry(**b))
                .is_none()
}

#[cfg(test)]
mod tests {

    use rstest::rstest;

    use crate::{GapError, DEFAULT_GAP_SIZE};

    use super::GapText;

    // TODO: split this into multiple cases or their own functions.
    // This takes wayyy to long to run with miri (less of a problem without miri but still slow).
    #[test]
    fn move_gap_start() -> Result<(), GapError> {
        let sample = String::from_utf8((0..128).collect()).unwrap().repeat(10);
        let mut t = GapText::new(sample.clone());
        t.insert_gap(64);
        for gs in 0..1280 {
            t.move_gap_start_to(gs)?;
            t.buf[t.gap.clone()].fill(0);
            assert_eq!(&t.buf[..t.gap.start], sample[..gs].as_bytes());
            assert_eq!(&t.buf[t.gap.end..], sample[gs..].as_bytes());
        }
        for gs in (0..1280).rev() {
            t.move_gap_start_to(gs)?;
            t.buf[t.gap.clone()].fill(0);
            assert_eq!(&t.buf[..t.gap.start], sample[..gs].as_bytes());
            assert_eq!(&t.buf[t.gap.end..], sample[gs..].as_bytes());
        }

        // Test case where the move difference is larger than the gap size.
        t.move_gap_start_to(0)?;
        t.buf[t.gap.clone()].fill(0);
        assert_eq!(&t.buf[DEFAULT_GAP_SIZE..], sample.as_bytes());
        t.move_gap_start_to(1200)?;
        t.buf[t.gap.clone()].fill(0);
        assert_eq!(&t.buf[..1200], sample[..1200].as_bytes());
        t.move_gap_start_to(0)?;
        t.buf[t.gap.clone()].fill(0);
        assert_eq!(&t.buf[..t.gap.start], sample[..t.gap.start].as_bytes());
        assert_eq!(&t.buf[DEFAULT_GAP_SIZE..], sample.as_bytes());

        Ok(())
    }

    #[rstest]
    #[case::empty_gap(0)]
    #[case::insertion_exceeds_gap(1)]
    #[case::insertion_fits_in_gap(5)]
    #[case::very_large_gap(1024)]
    fn insert(#[case] gap_size: usize) -> Result<(), GapError> {
        let sample = "Hello, World";
        let mut t = GapText::with_gap_size(sample.to_string(), gap_size);
        t.insert_gap(0);
        t.insert(3, "AAAAA")?;
        assert_eq!(&t.buf[..t.gap.start - 5], b"Hel");
        assert_eq!(&t.buf[t.gap.start - 5..t.gap.start], "AAAAA".as_bytes());
        assert_eq!(&t.buf[t.gap.end..], "lo, World".as_bytes());

        Ok(())
    }

    #[rstest]
    #[case::empty_gap(0)]
    #[case::small_gap(1)]
    #[case::small_gap(2)]
    #[case::small_gap(3)]
    #[case::medium_gap(128)]
    #[case::large_gap(512)]
    fn delete(#[case] gap_size: usize) -> Result<(), GapError> {
        let sample = "Hello, World";
        let mut t = GapText::with_gap_size(sample.to_string(), gap_size);
        t.insert_gap(10);
        // ", World"
        t.delete(0..5)?;
        assert_eq!(&t.buf[..t.gap.start], b"");
        assert_eq!(&t.buf[t.gap.end..], b", World");
        assert_eq!(t.gap.len(), gap_size + 5);
        assert_eq!(t.gap.start, 0);
        assert_eq!(t.gap.end, t.gap.start + 5 + gap_size);

        // ", Wd"
        t.delete(3..6)?;
        assert_eq!(std::str::from_utf8(&t.buf[..t.gap.start]).unwrap(), ", W");
        assert_eq!(std::str::from_utf8(&t.buf[t.gap.end..]).unwrap(), "d");
        assert_eq!(t.gap.len(), gap_size + 8);
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
    fn get_insert(#[case] gap_size: usize) {
        let sample = "Hello, World";
        let mut t = GapText::with_gap_size(sample.to_string(), gap_size);
        t.insert_gap(2);

        // "HeApplesllo, World"
        t.insert(2, "Apples").unwrap();
        let s = t.get(0..4).unwrap();
        assert_eq!(s, "HeAp");
        let s = t.get(2..10).unwrap();
        assert_eq!(s, "Applesll");
        let s = t.get(10..10).unwrap();
        assert_eq!(s, "");
        let s = t.get(10..15).unwrap();
        assert_eq!(s, "o, Wo");
        let s = t.get(..).unwrap();
        assert_eq!(s, "HeApplesllo, World");

        // "HeApplesOrangesllo, World"
        t.insert(8, "Oranges").unwrap();
        let s = t.get(0..4).unwrap();
        assert_eq!(s, "HeAp");
        let s = t.get(2..10).unwrap();
        assert_eq!(s, "ApplesOr");
        let s = t.get(10..10).unwrap();
        assert_eq!(s, "");
        let s = t.get(10..15).unwrap();
        assert_eq!(s, "anges");
        let s = t.get(..).unwrap();
        assert_eq!(s, "HeApplesOrangesllo, World");
    }
}
