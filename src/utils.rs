use std::{
    mem::MaybeUninit,
    ops::{Bound, Range, RangeBounds},
};

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

    if start > end || max < end || max <= start {
        ret_none();
        None
    } else {
        Some(start..end)
    }
}

/// Checks which slice the position is located in and returns ((first[..at], first[at..]), last) or
/// (first, (last[..at], last[at..]))
///
/// If the at position is before mid/after first, returns true
#[inline(always)]
pub(crate) fn get_parts_at<'a, T>(
    mut first: &'a [T],
    mut last: &'a [T],
    at: usize,
) -> (&'a [T], &'a [T], &'a [T], bool) {
    let (mid, before_mid) = if first.len() > at {
        let (f, mid) = first.split_at(at);
        first = f;
        (mid, true)
    } else {
        let (mid, l) = last.split_at(at - first.len());
        last = l;
        (mid, false)
    };
    (first, mid, last, before_mid)
}
