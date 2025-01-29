use crate::{raw_gap_buf::RawGapBuf, utils::get_parts_at};

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
        let gap_len = self.raw.gap_len();
        let s_bytes = s.as_bytes();
        if s.len() > gap_len {
            let [start, end] = self.raw.get_slices();
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
}

#[cfg(test)]
mod tests {
    use super::GapString;

    #[test]
    fn insert() {
        let mut gap_str = GapString::new();
        gap_str.insert("Hello", 0);
        assert_eq!(gap_str.raw.get_slices(), [b"Hello".as_slice(), b""])
    }
}
