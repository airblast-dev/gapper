use std::{mem::MaybeUninit, num::NonZeroUsize, ops::Range, ptr::NonNull};

use crate::utils::{get_range, is_get_single};

/// Similar to RawVec used in the standard library, this is our inner struct
///
/// Internally uses a boxed slice to allocate and deallocate. Once the allocator API is stabilized
/// this should be changed to use an allocator instead. This also removes a bunch of checks we
/// would normally have to do as the box will deal with it upon dropping.
pub(crate) struct RawGapBuf<T> {
    /// Using NonNull for Null pointer optimization
    start: NonNull<[T]>,
    end: NonNull<[T]>,
}

impl<T> Default for RawGapBuf<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

// compile time assertion to ensure that RawGapBuf is null pointer optimized
const _: () = assert!(
    core::mem::size_of::<RawGapBuf<NonZeroUsize>>()
        == core::mem::size_of::<Option<RawGapBuf<NonZeroUsize>>>()
);

impl<T> RawGapBuf<T> {
    const IS_ZST: bool = size_of::<T>() == 0;

    #[inline(always)]
    pub const fn new() -> Self {
        // SAFETY: ZST's are skipped during the deallocation of a Box, as such creating a dangling slice
        // pointer with a length of 0 allows us to make this function const
        let ptr = NonNull::slice_from_raw_parts(NonNull::dangling(), 0);
        Self {
            // use the same dangling pointer, otherwise gap size calculation might get messed up
            start: ptr,
            end: ptr,
        }
    }

    #[inline]
    pub fn new_with<const S: usize, const E: usize>(
        mut start: [T; S],
        gap_size: usize,
        mut end: [T; E],
    ) -> Self {
        let buf_ptr: Box<[MaybeUninit<T>]> = Box::new_uninit_slice(S + E + gap_size);
        let leaked = NonNull::from(Box::leak(buf_ptr)).cast::<T>();
        unsafe {
            leaked.copy_from_nonoverlapping(NonNull::from(&mut start).cast::<T>(), S);
            leaked
                .add(S + gap_size)
                .copy_from_nonoverlapping(NonNull::from(&mut end).cast::<T>(), E);

            core::mem::forget(start);
            core::mem::forget(end);

            Self {
                start: NonNull::slice_from_raw_parts(leaked, S),
                end: NonNull::slice_from_raw_parts(leaked.add(S + gap_size), E),
            }
        }
    }

    /// Initialize a [`RawGapBuf`] by byte copying from the source.
    ///
    /// Useful when reallocating the buffer.
    ///
    /// # Safety
    /// Calling source T's drop code is UB.
    #[inline]
    pub unsafe fn new_with_slice(start: &[&[T]], gap_size: usize, end: &[&[T]]) -> Self {
        let start_len = start.iter().map(|s| s.len()).sum();
        let end_len = end.iter().map(|s| s.len()).sum();
        let buf_ptr: Box<[MaybeUninit<T>]> = Box::new_uninit_slice(start_len + gap_size + end_len);
        let leaked = NonNull::from(Box::leak(buf_ptr)).cast::<T>();

        let mut i = 0;
        let mut offset = 0;

        while i < start.len() {
            let i_len = start[i].len();
            unsafe {
                leaked
                    .add(offset)
                    .copy_from_nonoverlapping(NonNull::from(start[i]).cast::<T>(), i_len)
            };
            i += 1;
            offset += i_len;
        }

        offset += gap_size;

        i = 0;
        while i < end.len() {
            let i_len = end[i].len();
            unsafe {
                leaked
                    .add(offset)
                    .copy_from_nonoverlapping(NonNull::from(end[i]).cast::<T>(), i_len)
            };
            i += 1;
            offset += i_len;
        }
        Self {
            start: NonNull::slice_from_raw_parts(leaked, start_len),
            end: unsafe {
                NonNull::slice_from_raw_parts(leaked.add(start_len + gap_size), end_len)
            },
        }
    }

    #[inline(always)]
    pub const fn get_parts(&self) -> [&[T]; 2] {
        unsafe { [self.start.as_ref(), self.end.as_ref()] }
    }

    #[inline(always)]
    pub const fn get_parts_mut(&mut self) -> [&mut [T]; 2] {
        unsafe { [self.start.as_mut(), self.end.as_mut()] }
    }

    #[inline(always)]
    pub fn get(&self, mut index: usize) -> Option<&T> {
        if index >= self.len() {
            return None;
        }
        index = self.start_with_offset(index);
        unsafe { Some((self.start_ptr().add(index)).as_ref()) }
    }

    /// Get a slice of the values in the range
    ///
    /// Shifts the items in the buffer to provide a contiguous slice for the provided range.
    ///
    /// Unlike [`RawGapBuf::to_slice`], this only moves the range out of the provided range and
    /// does minimal copying to accomplish this goal. If reading large or disjointed parts, this can be an
    /// expensive call as more elements will be needed to be shifting.
    /// This is mainly recommended for cases where the provided range is expected to be fairly small
    /// compared to the gap.
    ///
    /// If calling this in a loop, prefer using [`RawGapBuf::move_gap_out_of`] with the largest
    /// start and end values of the ranges, and then access the slices via this method.
    ///
    /// Returns None if the provided ranges are out of bounds.
    #[inline(always)]
    pub fn get_slice(&mut self, r: Range<usize>) -> Option<&[T]> {
        let r = get_range(self.len(), r)?;
        self.move_gap_out_of(r.start..r.end);
        debug_assert!(is_get_single(self.start_len(), r.start, r.end));
        let start_pos = self.start_with_offset(r.start);
        // SAFETY: get_range has validated the provided range and the gap has been moved out of
        // the range. it is now safe to create a slice from the start with offset with a length of
        // the range
        Some(unsafe {
            NonNull::slice_from_raw_parts(self.start_ptr().add(start_pos), r.end - r.start).as_ref()
        })
    }

    #[inline(always)]
    pub fn get_range(&self, r: Range<usize>) -> Option<[&[T]; 2]> {
        let len = self.len();
        if r.start >= len || r.end > len || r.start > r.end {
            return None;
        }

        let (start_pos, end_pos) = (self.start_with_offset(r.start), self.end_with_offset(r.end));

        if is_get_single(self.start_len(), start_pos, end_pos) {
            let single = unsafe {
                NonNull::slice_from_raw_parts(self.start_ptr().add(start_pos), r.end - r.start)
                    .as_ref()
            };
            return Some([single, &[]]);
        }

        let [start, end] = self.get_parts();
        unsafe {
            Some([
                start.get_unchecked(r.start..),
                end.get_unchecked(0..r.end - self.start_len()),
            ])
        }
    }

    #[inline(always)]
    #[allow(clippy::wrong_self_convention)]
    pub fn to_slice(&mut self) -> &[T] {
        self.move_gap_out_of(0..self.len());
        let [start, end] = self.get_parts();
        if !start.is_empty() {
            start
        } else {
            end
        }
    }

    #[inline(always)]
    pub fn to_slice_mut(&mut self) -> &mut [T] {
        self.move_gap_out_of(0..self.len());
        let [start, end] = self.get_parts_mut();
        if !start.is_empty() {
            start
        } else {
            end
        }
    }

    // the ptr methods are to avoid tons of casts in call sites, they are zero cost but this makes
    // it so we don't accidentally cast to a wrong type due to inference

    #[inline(always)]
    pub const fn start_ptr(&self) -> NonNull<T> {
        self.start.cast()
    }

    #[inline(always)]
    pub const fn start_ptr_mut(&mut self) -> NonNull<T> {
        self.start.cast()
    }

    #[inline(always)]
    pub const fn start(&self) -> NonNull<[T]> {
        self.start
    }

    #[inline(always)]
    pub const fn start_mut(&mut self) -> NonNull<[T]> {
        self.start
    }

    #[inline(always)]
    pub const fn start_len(&self) -> usize {
        self.start().len()
    }

    #[inline(always)]
    pub const fn end_ptr(&self) -> NonNull<T> {
        self.end.cast()
    }

    #[inline(always)]
    pub const fn end_ptr_mut(&mut self) -> NonNull<T> {
        self.end.cast()
    }

    #[inline(always)]
    pub const fn end(&self) -> NonNull<[T]> {
        self.end
    }

    #[inline(always)]
    pub const fn end_mut(&mut self) -> NonNull<[T]> {
        self.end
    }

    #[inline(always)]
    pub const fn end_len(&self) -> usize {
        self.end().len()
    }

    /// Returns the total length of both slices
    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.start_len() + self.end_len()
    }

    /// Returns true if both slices are empty
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a pointer to the possibly uninitialized gap
    ///
    /// This function explicity returns a pointer instead of a `&mut [T]` to allow specialized
    /// implementations (such as a string buffer) to do efficient copying without worrying about
    /// drop code.
    #[inline(always)]
    pub const fn spare_capacity_mut(&mut self) -> NonNull<[MaybeUninit<T>]> {
        unsafe {
            let gap_start = self.start.cast::<MaybeUninit<T>>().add(self.start.len());
            let gap_len = self.gap_len();
            NonNull::slice_from_raw_parts(gap_start, gap_len)
        }
    }

    /// Returns the current gap length
    #[inline(always)]
    pub const fn gap_len(&self) -> usize {
        // with ZST's there is no gap length, as such the subtraction below can overflow
        if Self::IS_ZST {
            return 0;
        }
        unsafe { self.end_ptr().offset_from(self.start_ptr()) as usize - self.start_len() }
    }

    /// Returns the length of the total allocation
    #[inline(always)]
    pub const fn total_len(&self) -> usize {
        // with ZST's there is no gap length, as such the addition below can overflow
        let len = self.len();
        if Self::IS_ZST {
            return len;
        }
        unsafe { (self.end_ptr().offset_from(self.start_ptr()) as usize) + self.end_len() }
    }

    /// Grow the start slice by the provided value
    ///
    /// # Safety
    /// Caller must ensure that the values are initialized, and that growing the start does not
    /// cause overlapping with the end.
    #[inline(always)]
    pub unsafe fn grow_start(&mut self, by: usize) {
        let start_len = self.start_len();
        let t_ptr = self.start_ptr();

        // ensure extending the start does not cause an overlap with the end pointer
        if !Self::IS_ZST {
            debug_assert!(
                t_ptr.add(start_len + by) <= self.end_ptr(),
                "cannot grow that start value as it overlaps with the end slice"
            );
        }
        self.start = NonNull::slice_from_raw_parts(t_ptr, start_len + by);
    }

    /// Shrink the start slice by the provided value
    ///
    /// # Safety
    /// Caller must ensure that the values are correctly dropped, the start length >= by, and that
    /// the pointer has enough provenance.
    #[inline(always)]
    pub unsafe fn shrink_start(&mut self, by: usize) {
        let start_len = self.start_len();

        // ensure shrinking the slice does not point out of bounds
        debug_assert!(
            start_len >= by,
            "cannot shrink start slice when shrink value is more than the total length"
        );
        self.start = NonNull::slice_from_raw_parts(self.start_ptr(), start_len - by);
    }

    /// Grow the end slice by the provided value
    ///
    /// # Safety
    /// Caller must ensure that the values before the end pointer are initialized, does not
    /// overlap with the start slice and that the pointer has enough provenance.
    #[inline(always)]
    pub unsafe fn grow_end(&mut self, by: usize) {
        let end_len = self.end_len();
        if !Self::IS_ZST {
            debug_assert!(
                self.gap_len() >= by,
                "cannot grow the end slice when the grow overlaps with the start slice"
            );
        }
        let t_ptr = self.end_ptr().sub(by);
        self.end = NonNull::slice_from_raw_parts(t_ptr, end_len + by);
    }

    /// Shrink the end slice by the provided value
    ///
    /// # Safety
    /// Caller must ensure that the values are correctly dropped, the end length >= by, and that
    /// the pointer has enough provenance.
    #[inline(always)]
    pub unsafe fn shrink_end(&mut self, by: usize) {
        let end_len = self.end_len();

        // ensure shrinking the slice does not point out of bounds
        debug_assert!(
            end_len >= by,
            "cannot shrink start slice when shrink value is more than the total length"
        );
        let t_ptr = unsafe { self.end_ptr().add(by) };
        self.end = NonNull::slice_from_raw_parts(t_ptr, end_len - by);
    }

    /// Shifts the gap by the provided value
    ///
    /// # Safety
    ///
    /// Same safety rules as shrink_*, and grow_* methods apply to this method as well.
    #[inline(always)]
    pub unsafe fn shift_gap(&mut self, by: isize) {
        // the only case where this can cause UB with correct values is when dealing with ZST's.
        // Since a box can store up to isize::MAX bytes this isn't a problem for non ZST types but a
        // slice or box can exceed isize::MAX length (not bytes) when ZST's are stored. Even though the pointer
        // math doesn't cause problems, the unchecked addition can cause UB so we handle the edge
        // case.
        if Self::IS_ZST {
            return;
        }
        // The unwrap_unchecked use below doesn't actually matter other than changing the assembly
        // output.
        //
        // Using shrink_* and grow_* wouldn't help the UB problem when incorrectly used as they
        // would point to out of bounds. The only difference here is we are able to optimize this
        // further with fairly similar risks.
        self.start = NonNull::slice_from_raw_parts(self.start_ptr(), unsafe {
            self.start_len().checked_add_signed(by).unwrap_unchecked()
        });
        self.end = NonNull::slice_from_raw_parts(self.end_ptr().offset(by), unsafe {
            self.end_len().checked_add_signed(-by).unwrap_unchecked()
        });
    }

    #[inline(always)]
    pub fn start_with_offset(&self, start: usize) -> usize {
        if start >= self.start_len() {
            start + self.gap_len()
        } else {
            start
        }
    }

    #[inline(always)]
    pub fn end_with_offset(&self, end: usize) -> usize {
        if end > self.start_len() {
            end + self.gap_len()
        } else {
            end
        }
    }

    /// Move the gap start position to the provided position
    ///
    /// Generally [`RawGapBuf::move_gap_out_of`] should be preferred as it avoids excessive
    /// copying.
    ///
    /// # Panics
    /// Panics if the provided gap position is greater than [`RawGapBuf::len`].
    pub fn move_gap_start_to(&mut self, to: usize) {
        assert!(to <= self.len());
        if self.start_len() == to {
            return;
        }

        // this code is pretty ugly, but results in pretty clean assembly with relatively little
        // branching
        //
        // TODO: should benchmark if this is even worth it
        let spare = self.spare_capacity_mut();
        let gap_len = spare.len();
        let spare = spare.cast::<T>();
        let shift: isize;
        // a tagged scope is used to reduce the branch count
        // the shift operation always happens, but src and dst cannot be overlapping
        // if they are overlapping exit the scope after copying, and just shift the slices.
        'ov: {
            let src;
            let dst;
            let copy_count;
            // move gap left
            if to < self.start_len() && self.start_len() - to <= gap_len {
                copy_count = self.start_len() - to;
                shift = -(copy_count as isize);
                unsafe {
                    src = self.start_ptr().add(self.start_len() - copy_count);
                    dst = spare.add(gap_len - copy_count);
                }
            }
            // move gap right
            else if to > self.start_len() && to - self.start_len() <= gap_len {
                copy_count = to - self.start_len();
                src = self.end_ptr();
                dst = spare;
                shift = copy_count as isize;
            } else {
                // move gap right
                let (src, dst, copy_count) = if to >= self.start_len() {
                    copy_count = to - self.start_len();
                    shift = copy_count as isize;

                    (self.end_ptr(), spare, copy_count)
                }
                // move gap left
                else {
                    copy_count = self.start_len() - to;
                    shift = -(copy_count as isize);
                    unsafe {
                        (
                            self.start_ptr().add(to),
                            self.start_ptr().add(to + gap_len),
                            copy_count,
                        )
                    }
                };

                unsafe { src.copy_to(dst, copy_count) };
                // the copy is not non overlapping so we did it right above
                // skip the copy call right below and just shift the gap
                break 'ov;
            }

            // debug assertion in case there is a logic error above
            debug_assert!(
                unsafe { src.offset_from(dst).unsigned_abs() >= copy_count },
                "attempted to copy overlapping pointers"
            );
            unsafe { src.copy_to_nonoverlapping(dst, copy_count) };
        }

        unsafe { self.shift_gap(shift) };
    }

    /// Move the gap out of a range
    ///
    /// Determines the position to move the gap whilst moving it out of the range, and doing
    /// minimal copies.
    ///
    /// Returns true if the provided range is now on the left side.
    #[inline(always)]
    pub fn move_gap_out_of(&mut self, r: Range<usize>) -> bool {
        // i dont like returning an option bool here
        // maybe require the higher level type to check for the single get case?
        assert!(self.total_len() >= r.end && r.start <= r.end);
        // shift the gap out of the specified range whilst doing minimal amount of copying
        if r.start > self.start_len() {
            return true;
        } else if r.end <= self.start_len() {
            return false;
        }

        // determine the minimum copies needed to move the gap out of the range
        let to_right_copy = self.start_len() - r.start;
        let to_left_copy = r.end - self.start_len();
        let is_left;
        let move_to = if to_right_copy > to_left_copy {
            is_left = true;
            r.end
        } else {
            is_left = false;
            r.start
        };
        self.move_gap_start_to(move_to);

        is_left
    }

    /// Drop's Self, calling the drop code of the stored T
    pub fn drop_in_place(mut self) {
        // SAFETY: after dropping the T's, self also gets dropped at the end of the function so no
        // access is performed to the inner T's
        unsafe { self.drop_t() };
    }

    /// Call the drop code for the stored T
    ///
    /// # Safety
    /// Accessing any T stored in [`RawGapBuf`] after this is called is UB.
    pub unsafe fn drop_t(&mut self) {
        unsafe {
            self.start.drop_in_place();
            self.end.drop_in_place();
        }
    }
}

// This implementation allows us to cover every single From implementation for a boxed slice
impl<T> Clone for RawGapBuf<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let start_len = self.start_len();
        let gap_len = self.gap_len();
        let end_len = self.end_len();
        let buf: Box<[MaybeUninit<T>]> = Box::new_uninit_slice(start_len + gap_len + end_len);
        let leaked = NonNull::from(Box::leak(buf)).cast::<T>();
        unsafe {
            let [start, end] = self.get_parts();
            for (i, item) in start.iter().enumerate() {
                leaked.add(i).write(item.clone());
            }

            let end_start = leaked.add(start_len + gap_len);

            for (i, item) in end.iter().enumerate() {
                end_start.add(i).write(item.clone());
            }

            Self {
                start: NonNull::slice_from_raw_parts(leaked, start_len),
                end: NonNull::slice_from_raw_parts(end_start, end_len),
            }
        }
    }
}

impl<T, A> From<A> for RawGapBuf<T>
where
    Box<[T]>: From<A>,
{
    #[inline]
    fn from(value: A) -> Self {
        let buf: Box<[T]> = Box::from(value);
        let val_len = buf.len();

        // The box will be dropped manually as part of RawGapBuf's drop implementation
        let start_ptr = NonNull::from(Box::leak(buf)).cast::<T>();

        unsafe {
            Self {
                start: NonNull::slice_from_raw_parts(start_ptr, val_len),
                end: NonNull::slice_from_raw_parts(start_ptr.add(val_len), 0),
            }
        }
    }
}

impl<T> Drop for RawGapBuf<T> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            let total_len = self.total_len();

            // only deal with the box's allocation
            // the drop code of T should be handled by a higher level type
            //
            // reconstruct the box using the total length and MaybeUninit to have correct
            // alignment and size whilst avoiding calling T's drop code.
            //
            // SAFETY: MaybeUninit is guaranteed to have the same layout as T
            let ptr = NonNull::slice_from_raw_parts(
                self.start_ptr_mut().cast::<MaybeUninit<T>>(),
                total_len,
            );

            drop(Box::<[MaybeUninit<T>]>::from_raw(ptr.as_ptr()));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::RawGapBuf;

    #[test]
    fn new() {
        let s_buf: RawGapBuf<String> = RawGapBuf::new();
        assert_eq!(s_buf.start_ptr(), s_buf.end_ptr());
        assert_eq!(s_buf.start_ptr(), s_buf.end_ptr());
    }

    #[test]
    fn get_parts() {
        let s_buf: RawGapBuf<String> = RawGapBuf::new();
        let [start, end] = s_buf.get_parts();
        assert!(start.is_empty());
        assert!(end.is_empty());
    }

    #[test]
    fn get_parts_mut() {
        let mut s_buf: RawGapBuf<String> = RawGapBuf::new();
        let [start, end] = s_buf.get_parts_mut();
        assert!(start.is_empty());
        assert!(end.is_empty());
    }

    #[test]
    fn gap_len() {
        let s_buf: RawGapBuf<String> = RawGapBuf::new();
        assert_eq!(s_buf.gap_len(), 0);
        let s_buf: RawGapBuf<String> = RawGapBuf::from(["Hello".to_string()].as_slice());
        assert_eq!(s_buf.gap_len(), 0);
        s_buf.drop_in_place();
    }

    #[test]
    fn total_len() {
        let s_buf = RawGapBuf::from(["Hi"]);
        assert_eq!(1, s_buf.total_len());
    }

    #[test]
    fn from_slice() {
        let s_buf: RawGapBuf<String> = RawGapBuf::from(["Hello".to_string()].as_slice());
        s_buf.drop_in_place();
    }

    #[test]
    fn from_box_slice() {
        let s_buf: RawGapBuf<String> = RawGapBuf::from(Box::from(["Hello".to_string()]));
        s_buf.drop_in_place();
    }

    #[test]
    fn clone() {
        let s_buf: RawGapBuf<String> = RawGapBuf::from(["Hello".to_string(), "Bye".to_string()]);
        let cloned_s_buf = s_buf.clone();
        assert_eq!(s_buf.get_parts(), cloned_s_buf.get_parts());
        s_buf.drop_in_place();
        cloned_s_buf.drop_in_place();
    }

    #[test]
    fn new_with() {
        let s_buf = RawGapBuf::new_with(
            ["Hi", "Bye"].map(String::from),
            10,
            ["1", "2", "3"].map(String::from),
        );
        assert_eq!(
            s_buf.get_parts(),
            [["Hi", "Bye"].as_slice(), ["1", "2", "3"].as_slice()]
        );

        assert_eq!(s_buf.gap_len(), 10);

        s_buf.drop_in_place();
    }

    #[test]
    fn new_with_slice() {
        let s_buf = unsafe {
            RawGapBuf::new_with_slice(
                &[[1, 2, 3].as_slice(), [4, 5, 6].as_slice()],
                10,
                &[[7, 8, 9].as_slice(), [10, 11, 12].as_slice()],
            )
        };
        assert_eq!(
            s_buf.get_parts(),
            [
                [1, 2, 3, 4, 5, 6].as_slice(),
                [7, 8, 9, 10, 11, 12].as_slice()
            ]
        );

        assert_eq!(s_buf.gap_len(), 10);
    }

    #[test]
    fn start_with_offset() {
        let s_buf = RawGapBuf::new_with(["a", "b", "c"], 3, ["1", "2"]);
        for i in 0..3 {
            assert_eq!(s_buf.start_with_offset(i), i);
        }
        for i in 3..8 {
            assert_eq!(s_buf.start_with_offset(i), i + 3);
        }
    }

    #[test]
    fn end_with_offset() {
        let s_buf = RawGapBuf::new_with(["a", "b", "c"], 3, ["1", "2"]);
        for i in 0..4 {
            assert_eq!(s_buf.end_with_offset(i), i);
        }
        for i in 4..9 {
            assert_eq!(s_buf.end_with_offset(i), i + 3);
        }
    }

    #[test]
    fn move_gap_start_to() {
        let mut s_buf = RawGapBuf::new_with(
            ["1", "2", "3"].map(String::from),
            2,
            ["a", "b", "c"].map(String::from),
        );

        // move gap to start
        s_buf.move_gap_start_to(0);
        assert_eq!(
            s_buf.get_parts(),
            [[].as_slice(), ["1", "2", "3", "a", "b", "c"].as_slice()]
        );

        // move gap to end
        s_buf.move_gap_start_to(6);
        assert_eq!(
            s_buf.get_parts(),
            [["1", "2", "3", "a", "b", "c"].as_slice(), [].as_slice()]
        );

        // move the gap by an amount that fits the gap backward
        s_buf.move_gap_start_to(4);
        assert_eq!(
            s_buf.get_parts(),
            [["1", "2", "3", "a"].as_slice(), ["b", "c"].as_slice()]
        );

        // move the gap by an amount that fits the gap forward 2x
        s_buf.move_gap_start_to(2);
        assert_eq!(
            s_buf.get_parts(),
            [["1", "2"].as_slice(), ["3", "a", "b", "c"].as_slice()]
        );

        s_buf.move_gap_start_to(0);
        assert_eq!(
            s_buf.get_parts(),
            [[].as_slice(), ["1", "2", "3", "a", "b", "c"].as_slice()]
        );

        // move the gap by an amount that doesnt fit in the gap forward
        s_buf.move_gap_start_to(4);
        assert_eq!(
            s_buf.get_parts(),
            [["1", "2", "3", "a"].as_slice(), ["b", "c"].as_slice()]
        );

        // move the gap by an amount that doesnt fit in the gap backward
        s_buf.move_gap_start_to(1);
        assert_eq!(
            s_buf.get_parts(),
            [["1"].as_slice(), ["2", "3", "a", "b", "c"].as_slice()]
        );

        s_buf.drop_in_place();
    }

    #[test]
    fn move_gap_out_of() {
        let mut s_buf = RawGapBuf::new_with(["1", "2", "3"], 10, ["4", "5", "6", "7"]);
        s_buf.move_gap_out_of(1..5);
        assert_eq!(
            s_buf.get_parts(),
            [["1"].as_slice(), ["2", "3", "4", "5", "6", "7"].as_slice()]
        );

        // this test doesn't just validate the results slice's validity
        // it also checks if we are moving the minimal elements needed
        s_buf.move_gap_out_of(0..s_buf.len());
        assert_eq!(
            s_buf.get_parts(),
            [
                [].as_slice(),
                ["1", "2", "3", "4", "5", "6", "7"].as_slice()
            ]
        );

        s_buf.move_gap_out_of(1..s_buf.len());
        assert_eq!(
            s_buf.get_parts(),
            [
                [].as_slice(),
                ["1", "2", "3", "4", "5", "6", "7"].as_slice(),
            ]
        );
    }

    #[test]
    fn to_slice() {
        let mut s_buf: RawGapBuf<u8> = RawGapBuf::new_with([], 0, []);
        let s = s_buf.to_slice();
        assert!(s.is_empty());

        let mut s_buf: RawGapBuf<u8> = RawGapBuf::new_with([1, 2, 3], 0, [4, 5, 6]);
        let s = s_buf.to_slice();
        assert_eq!(s, &[1, 2, 3, 4, 5, 6]);

        let mut s_buf: RawGapBuf<u8> = RawGapBuf::new_with([1, 2, 3], 1, []);
        let s = s_buf.to_slice();
        assert_eq!(s, &[1, 2, 3]);

        let mut s_buf: RawGapBuf<u8> = RawGapBuf::new_with([], 1, [1, 2, 3]);
        let s = s_buf.to_slice();
        assert_eq!(s, &[1, 2, 3]);

        let mut s_buf: RawGapBuf<u8> = RawGapBuf::new_with([1, 2, 3], 1, [4, 5, 6, 7, 8]);
        let s = s_buf.to_slice();
        assert_eq!(s, &[1, 2, 3, 4, 5, 6, 7, 8]);
    }

    #[test]
    fn get() {
        let s_buf = RawGapBuf::new_with([1, 2, 3], 10, [4, 5]);
        assert_eq!(s_buf.get(0), Some(&1));
        assert_eq!(s_buf.get(1), Some(&2));
        assert_eq!(s_buf.get(2), Some(&3));
        assert_eq!(s_buf.get(3), Some(&4));
        assert_eq!(s_buf.get(4), Some(&5));
        assert_eq!(s_buf.get(5), None);
        assert_eq!(s_buf.get(6), None);
    }

    // this is pretty stupid as the range isn't iterated over and a user can easily construct such
    // a range
    //
    // no idea why clippy is complaining about this
    // reading the lint information, it seems a range is treated as an iterator an not a
    // range?
    // https://rust-lang.github.io/rust-clippy/master/index.html#reversed_empty_ranges
    #[test]
    #[allow(clippy::reversed_empty_ranges)]
    fn get_range() {
        let s_buf = RawGapBuf::new_with([1, 2, 3], 10, [4, 5]);

        // check if all values stored are returned
        assert_eq!(
            s_buf.get_range(0..s_buf.len()),
            Some([[1, 2, 3].as_slice(), [4, 5].as_slice()]),
        );
        assert_eq!(s_buf.get_range(0..s_buf.len()), Some(s_buf.get_parts()));

        // get empty range
        for i in 0..5 {
            assert_eq!(s_buf.get_range(i..i), Some([[].as_slice(), &[]]));
        }
        assert_eq!(s_buf.get_range(5..5), None);
        assert_eq!(s_buf.get_range(6..6), None);

        // get single item as slice
        assert_eq!(s_buf.get_range(3..4), Some([[4].as_slice(), &[]]));
        assert_eq!(s_buf.get_range(4..5), Some([[5].as_slice(), &[]]));
        assert_eq!(s_buf.get_range(5..6), None);

        // get items across the gap
        assert_eq!(
            s_buf.get_range(1..5),
            Some([[2, 3].as_slice(), [4, 5].as_slice()])
        );

        // get items with reversed range
        assert_eq!(s_buf.get_range(6..4), None);
    }

    #[test]
    fn get_slice() {
        let mut s_buf = RawGapBuf::new_with([1, 2, 3], 10, [4, 5, 6]);

        assert_eq!(s_buf.get_slice(0..0).unwrap(), &[]);
        assert_eq!(s_buf.get_parts(), [&[1, 2, 3], &[4, 5, 6]]);
        assert_eq!(s_buf.get_slice(0..1).unwrap(), &[1]);
        assert_eq!(s_buf.get_parts(), [&[1, 2, 3], &[4, 5, 6]]);
        assert_eq!(s_buf.get_slice(1..2).unwrap(), &[2]);
        assert_eq!(s_buf.get_parts(), [&[1, 2, 3], &[4, 5, 6]]);
        assert_eq!(s_buf.get_slice(2..3).unwrap(), &[3]);
        assert_eq!(s_buf.get_parts(), [&[1, 2, 3], &[4, 5, 6]]);

        // these tests don't just validate the results but also check if the shifting was performed
        // with minimal copies.
        assert_eq!(s_buf.get_slice(2..5).unwrap(), &[3, 4, 5]);
        assert_eq!(
            s_buf.get_parts(),
            [[1, 2].as_slice(), [3, 4, 5, 6].as_slice()]
        );

        assert_eq!(s_buf.get_slice(0..3).unwrap(), &[1, 2, 3]);
        assert_eq!(
            s_buf.get_parts(),
            [[1, 2, 3].as_slice(), [4, 5, 6].as_slice()]
        );

        assert_eq!(s_buf.get_slice(0..5).unwrap(), &[1, 2, 3, 4, 5]);
        assert_eq!(
            s_buf.get_parts(),
            [[1, 2, 3, 4, 5].as_slice(), [6].as_slice()]
        );
    }
}
