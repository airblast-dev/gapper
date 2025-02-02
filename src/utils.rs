use std::ops::{Bound, Range, RangeBounds};

#[inline(always)]
pub(crate) fn u8_is_char_boundary(u: u8) -> bool {
    (u as i8) >= -0x40
}

#[inline(always)]
pub(crate) fn is_get_single(gap_start: usize, start: usize, end: usize) -> bool {
    end <= gap_start || gap_start <= start
}

#[inline(always)]
pub(crate) fn get_range<RB: RangeBounds<usize>>(max: usize, r: RB) -> Option<Range<usize>> {
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

    #[cold]
    #[inline(never)]
    fn ret_none() {}

    if start > end || max < end || max < start {
        ret_none();
        None
    } else {
        Some(start..end)
    }
}
