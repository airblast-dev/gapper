mod eol_indexes;
mod lines;
mod utils;

use std::ops::{Index, Range};

use eol_indexes::EolIndexes;
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
    read_buf: String,
}

impl GapText {
    fn new(s: String) -> Self {
        Self {
            buf: s.into_bytes(),
            read_buf: String::new(),
            gap: 0..0,
            base_gap_size: DEFAULT_GAP_SIZE,
        }
    }

    fn with_gap_size(s: String, size: usize) -> Self {
        Self {
            buf: s.into_bytes(),
            read_buf: String::new(),
            gap: 0..0,
            base_gap_size: size,
        }
    }

    fn gap_size(&self) -> usize {
        self.base_gap_size
    }

    fn set_gap_size(&mut self, gap_size: usize) {
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

        let mut left_shift = 0;
        let mut right_shift = 0;
        let (src_addr_offset, dst_addr_offset, copy_count): (usize, usize, usize) =
            if self.gap.contains(&to) {
                let copy_count = to - self.gap.start;
                right_shift = copy_count;
                (self.gap.end, self.gap.start, copy_count)
            } else if self.gap.end < to
                && to < self.gap.end + self.gap.len()
                && self.gap.start < to
                // we do this check to be able to use `std::ptr::copy_nonoverlapping` below.
                // if this condition is the one that returns false it will go to the fallback
                && to - self.gap.start <= self.gap.len()
            {
                // TODO: test the branch
                dbg!(&self.gap);
                let copy_count = to - self.gap.start;
                right_shift = copy_count;
                (self.gap.end, self.gap.start, copy_count)
            } else if to < self.gap.start && self.gap.start - to <= self.gap.len() {
                let copy_count = self.gap.start - to;
                left_shift = copy_count;
                (to, self.gap.end - copy_count, copy_count)
            } else {
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
            };

        #[cold]
        #[inline(never)]
        fn invalid_offset(len: usize, src_offset: usize, dst_offset: usize) -> ! {
            let max_offset = src_offset.max(dst_offset);
            panic!("len is {}, but pointer offset is {}", len, max_offset);
        }

        dbg!(to);
        dbg!(copy_count);
        dbg!(src_addr_offset);
        dbg!(dst_addr_offset);
        if self.buf.len() <= src_addr_offset.max(dst_addr_offset) + copy_count
            || src_addr_offset.abs_diff(dst_addr_offset) < copy_count
        {
            // this should never run, in case a bug is present above this avoids undefined behavior
            invalid_offset(self.buf.len(), src_addr_offset, dst_addr_offset);
        }

        unsafe {
            std::ptr::copy_nonoverlapping(
                self.buf.as_ptr().add(src_addr_offset),
                self.buf.as_mut_ptr().add(dst_addr_offset),
                copy_count,
            );
        }
        self.shift_gap_right(right_shift);
        self.shift_gap_left(left_shift);

        Ok(())
    }

    fn shift_gap_right(&mut self, by: usize) {
        self.gap.start += by;
        self.gap.end += by;
    }
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

    fn byte_pos_with_offset(&self, byte_pos: usize) -> usize {
        if self.gap.start > byte_pos {
            byte_pos
        } else if self.gap.contains(&byte_pos) {
            byte_pos - self.gap.start + self.gap.end
        } else {
            self.gap.len() + byte_pos
        }
    }
}

#[cfg(test)]
mod tests {

    use rstest::rstest;

    use crate::{GapError, DEFAULT_GAP_SIZE};

    use super::GapText;

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
}
