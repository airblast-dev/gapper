use std::{
    mem::MaybeUninit,
    ops::{Bound, Range, RangeBounds},
};

#[inline(always)]
pub(crate) fn u8_is_char_boundry(u: u8) -> bool {
    const CHAR_BOUNDRY_MASK: u8 = 192;
    u < 0x80 || u & CHAR_BOUNDRY_MASK == CHAR_BOUNDRY_MASK
}

#[inline(always)]
pub(crate) fn box_with_gap(b1: &[u8], gap_len: usize, b2: &[u8]) -> Box<[u8]> {
    let mut uninit = Box::new_uninit_slice(b1.len() + gap_len + b2.len());
    unsafe {
        uninit
            .as_mut_ptr()
            .copy_from_nonoverlapping(b1.as_ptr() as *const MaybeUninit<u8>, b1.len());
        uninit.as_mut_ptr().add(b1.len()).write_bytes(0, gap_len);
        uninit
            .as_mut_ptr()
            .add(b1.len() + gap_len)
            .copy_from_nonoverlapping(b2.as_ptr() as *const MaybeUninit<u8>, b2.len());
        uninit.assume_init()
    }
}

#[macro_export]
macro_rules! box_with_gap {
    ($gap_size:expr, $gap_pos:literal, $($slice:expr),*) => {
        {
            let gap_size = $gap_size;
            let slices = [$(&$slice),*];
            const SLICE_COUNT: usize = count_slices!($($slice,)*);
            let total_len = {
                let mut i = 0;
                let mut len = gap_size;
                while i <  SLICE_COUNT {
                    len += slices[i].len();
                    i += 1;
                }
                len
            };
            let mut uninit = ::std::boxed::Box::new_uninit_slice(total_len);
            let mut i = 0;
            let mut offset = 0;
            while i < $gap_pos {
                let slice_len = slices[i].len();
                unsafe{
                    uninit
                        .as_mut_ptr()
                        .add(offset)
                        .copy_from_nonoverlapping(
                            slices[i].as_ptr() as *const ::core::mem::MaybeUninit<u8>,
                            slice_len
                        );
                }
                offset += slice_len;
                i+=1;
            }

            unsafe {
                uninit.as_mut_ptr().add(offset).write_bytes(0, gap_size);
                offset += gap_size;
            }

            while i < SLICE_COUNT {
                let s_len = slices[i].len();
                unsafe {
                    uninit
                        .as_mut_ptr()
                        .add(offset)
                        .copy_from_nonoverlapping(
                            slices[i].as_ptr() as *const ::core::mem::MaybeUninit<u8>,
                            s_len
                        );
                    offset += slices[i].len();
                    i += 1;
                }
            }

            unsafe {
                uninit.assume_init()
            }
        }

    };
}

#[macro_export]
macro_rules! count_slices {
    ($slice:expr, $($other:expr,)*) => {
        1 + count_slices!($($other,)*)
    };
    () => {
        0
    }
}

#[inline(always)]
pub(crate) fn is_get_single(gap_start: usize, start: usize, end: usize) -> bool {
    end <= gap_start || gap_start <= start
}

#[inline(always)]
pub(crate) fn is_get_char_boundry(buf: &[u8], b1: u8, end_index: usize) -> bool {
    u8_is_char_boundry(b1)
            // NOTE: Option::is_none_or is more elegant but requires higher MSRV
            && buf
                .get(end_index)
                .filter(|b| !u8_is_char_boundry(**b))
                .is_none()
}

#[inline(always)]
pub(crate) fn is_get_str_valid(
    r: Range<usize>,
    buf: &[u8],
    gap: Range<usize>,
) -> Option<(usize, usize)> {
    // check the range values
    let s_len = buf.len() - gap.len();
    if s_len < r.end {
        return None;
    }

    let start_with_offset = start_byte_pos_with_offset(gap.clone(), r.start);
    let end_with_offset = end_byte_pos_with_offset(gap.clone(), r.end);

    debug_assert!(start_with_offset <= end_with_offset);

    // perform char boundry check
    if !is_get_char_boundry(buf, buf[start_with_offset], end_with_offset) {
        return None;
    }

    Some((start_with_offset, end_with_offset))
}

/// Returns the byte position for a start byte, adding the offset if needed.
#[inline(always)]
pub(crate) fn start_byte_pos_with_offset(gap: Range<usize>, byte_pos: usize) -> usize {
    if gap.start > byte_pos {
        byte_pos
    } else {
        gap.len() + byte_pos
    }
}

/// Returns the byte position for a end byte, adding the offset if needed.
#[inline(always)]
pub(crate) fn end_byte_pos_with_offset(gap: Range<usize>, byte_pos: usize) -> usize {
    if gap.start >= byte_pos {
        byte_pos
    } else {
        gap.len() + byte_pos
    }
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

    if start > end {
        ret_none();
        None
    } else {
        Some(start..end)
    }
}


/// Checks which slice the position is located in and returns ((first[..at], first[at..]), last) or
/// (first, (last[..at], last[at..]))
#[inline(always)]
pub(crate) fn get_parts_at<'a>(
    mut first: &'a [u8],
    mut last: &'a [u8],
    at: usize,
) -> (&'a [u8], &'a [u8], &'a [u8]) {
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
}
