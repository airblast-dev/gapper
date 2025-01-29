use std::{ops::RangeBounds, str::from_utf8_unchecked};

use crate::{
    raw_gap_buf::RawGapBuf,
    utils::{get_parts_at, get_range, u8_is_char_boundary},
};

const DEFAULT_GAP_SIZE: usize = 4096;

#[derive(Clone)]
pub struct GapString {
    raw: RawGapBuf<u8>,
}

impl GapString {
    #[inline]
    pub const fn new() -> Self {
        Self {
            raw: RawGapBuf::new(),
        }
    }

    fn insert(&mut self, s: &str, at: usize) {
        let at_byte = self.raw.get(at);

        // The insert position must be at a char boundary or at the end.
        assert!(at == self.raw.len() || at_byte.copied().is_some_and(u8_is_char_boundary));
        let gap_len = self.raw.gap_len();
        let s_bytes = s.as_bytes();
        if s.len() > gap_len {
            let [start, end] = self.raw.get_parts();
            let (start, mid, end, before_mid) = get_parts_at(start, end, at);
            let new_raw = if before_mid {
                RawGapBuf::new_with_slice([start, s_bytes], DEFAULT_GAP_SIZE, [mid, end])
            } else {
                RawGapBuf::new_with_slice([start, mid, s_bytes], DEFAULT_GAP_SIZE, [end])
            };
            self.raw = new_raw;
            return;
        }

        self.raw.move_gap_start_to(at);
        let spare = self.raw.spare_capacity_mut().cast::<u8>().as_ptr();
        let s_ptr = s.as_bytes().as_ptr();

        // The function requires that the provided slice does not overlap
        // it is safe to copy non overlapping
        unsafe { spare.copy_from_nonoverlapping(s_ptr, s.len()) };
        unsafe { self.raw.grow_start(s.len()) };
    }

    #[inline]
    fn get<RB: RangeBounds<usize>>(&self, r: RB) -> Option<[&str; 2]> {
        let r = get_range(self.raw.len(), r)?;
        if !self.is_get_char_boundary(r.start, r.end) {
            return None;
        }

        let [start, end] = self.raw.get_slice(r)?;
        // SAFETY: we return early if the positions are not on a char boundary the slices are now
        // guaranteed valid UTF-8 encoded bytes
        unsafe { Some([from_utf8_unchecked(start), from_utf8_unchecked(end)]) }
    }

    #[inline(always)]
    pub const fn get_parts(&self) -> [&str; 2] {
        let [start, end] = self.raw.get_parts();
        // SAFETY: the gap is always on a char boundary, as such the slice returned is guaranteed
        // to be valid UTF-8 encoded bytes
        unsafe { [from_utf8_unchecked(start), from_utf8_unchecked(end)] }
    }

    #[inline(always)]
    pub fn is_get_char_boundary(&self, start: usize, end: usize) -> bool {
        self.raw.get(start).is_some_and(|b| u8_is_char_boundary(*b))
            && (self.raw.get(end).is_some_and(|b| u8_is_char_boundary(*b)) || self.raw.len() == end)
    }
}

#[cfg(test)]
mod tests {
    use super::GapString;

    #[test]
    fn insert() {
        let mut gap_str = GapString::new();
        gap_str.insert("Hello", 0);
        assert_eq!(gap_str.get_parts(), ["Hello", ""]);

        gap_str.insert("Bye", 3);
        assert_eq!(gap_str.get_parts(), ["HelBye", "lo"]);

        gap_str.insert("123", 7);
        assert_eq!(gap_str.get_parts(), ["HelByel123", "o"]);
    }
}
