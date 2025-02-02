use std::{
    cmp::Ordering,
    ops::{Range, RangeBounds},
    ptr::NonNull,
    str::{from_utf8_unchecked, Chars},
};

use crate::{
    grower::Grower,
    raw_gap_buf::RawGapBuf,
    utils::{get_range, u8_is_char_boundary},
};

#[derive(Clone)]
struct GrowingGapString<G: Grower<str>> {
    buf: RawGapBuf<u8>,
    grower: G,
}

impl<G: Grower<str>> GrowingGapString<G> {
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

    #[inline]
    pub const fn with_grower(grower: G) -> Self {
        Self {
            buf: RawGapBuf::new(),
            grower,
        }
    }

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

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.buf.len()
    }

    #[inline(always)]
    pub fn gap_len(&self) -> usize {
        self.buf.gap_len()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn get<RB: RangeBounds<usize>>(&self, r: RB) -> Option<[&str; 2]> {
        let r = get_range(self.buf.len(), r)?;
        if !self.is_get_char_boundary(r.start..r.end) {
            return None;
        }

        let [start, end] = self.buf.get_range(r)?;
        unsafe { Some([from_utf8_unchecked(start), from_utf8_unchecked(end)]) }
    }

    #[inline]
    pub fn get_slice<RB: RangeBounds<usize>>(&mut self, r: RB) -> Option<&str> {
        let r = get_range(self.buf.len(), r)?;
        if !self.is_get_char_boundary(r.start..r.end) {
            return None;
        }
        let s = self.buf.get_slice(r)?;
        unsafe { Some(from_utf8_unchecked(s)) }
    }

    #[inline(always)]
    pub fn get_parts(&self) -> [&str; 2] {
        self.buf.get_parts().map(|s| unsafe {
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

    pub fn insert(&mut self, s: &str, at: usize) {
        assert!(
            self.buf.get(at).copied().is_some_and(u8_is_char_boundary) || self.buf.len() == at,
            "insertion should always be on a char boundary"
        );
        let [start, end] = self.buf.get_parts().map(|s| unsafe {
            // SAFETY: we do not allow the gap to be positioned between char boundaries both
            // parts are always valid UTF-8 string slice
            from_utf8_unchecked(s)
        });
        let base_gap_size = self.grower.base_gap_size(start, end);
        if self.buf.gap_len() < s.len() {
            self.buf.grow_gap(base_gap_size + s.len());
        }
        self.buf.move_gap_start_to(at);

        unsafe {
            // SAFETY: the references do not overlap and both are correctly aligned
            // we have allocated enough space above
            self.buf
                .spare_capacity_mut()
                .cast::<u8>()
                .copy_from_nonoverlapping(NonNull::from(s).cast::<u8>(), s.len());
            // SAFETY: we have initialized the gaps first s.len items it is now safe to grow the
            // start
            self.buf.grow_start(s.len());
        };
    }

    pub fn drain<RB: RangeBounds<usize>>(&mut self, r: RB) -> Chars {
        let r = get_range(self.buf.len(), r)
            .expect("range should never be out of bounds when draining");
        assert!(self.is_get_char_boundary(r.start..r.end));
        self.buf.move_gap_start_to(r.end);
        let start_ptr = self.buf.get_parts()[0].as_ptr();
        unsafe { self.buf.shrink_start(r.len()) };
        let s = unsafe { from_utf8_unchecked(core::slice::from_raw_parts(start_ptr, r.len())) };
        s.chars()
    }

    pub fn replace_range<RB: RangeBounds<usize>>(&mut self, r: RB, s: &str) {
        let r = get_range(self.buf.len(), r).expect("out of bounds range for replace_range");
        assert!(self.is_get_char_boundary(r.start..r.end));
        match r.len().cmp(&s.len()) {
            Ordering::Greater => {
                self.buf.move_gap_start_to(r.end);
                unsafe {
                    // SAFETY: we just checked the bounds above
                    self.buf.get_parts_mut()[0]
                        .get_unchecked_mut(r.start..r.start + s.len())
                        .copy_from_slice(s.as_bytes());
                    // SAFETY: we checked the bounds above and r.len is greater than s.len so no
                    // overflow can occur
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
                // SAFETY: the source is correctly aligned and we know that the slice is not
                // overlapping
                // we have shifted the gap to the end of the range and we are not overwriting the
                // contents of the end slice
                unsafe {
                    self.buf
                        .start_ptr()
                        .add(r.start)
                        .copy_from_nonoverlapping(NonNull::from(s).cast::<u8>(), s.len());
                    self.buf.grow_start(needed_space);
                };
            }
            Ordering::Equal => {
                // SAFETY: we just checked the bounds above
                unsafe { self.buf.get_slice(r.start..r.end).unwrap_unchecked() }
                    .copy_from_slice(s.as_bytes());
            }
        }
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
