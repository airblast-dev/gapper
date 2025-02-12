use std::{
    mem::{size_of, MaybeUninit},
    num::NonZeroUsize,
    ops::Range,
    ptr::NonNull,
};

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
    #[cfg(test)]
    pub fn new_with<const S: usize, const E: usize>(
        start: [T; S],
        gap_size: usize,
        end: [T; E],
    ) -> Self {
        let total_len = start.len() + end.len() + gap_size;
        let alloc_box = Box::leak(Box::<[T]>::new_uninit_slice(total_len));
        for (i, item) in start.into_iter().enumerate() {
            alloc_box[i].write(item);
        }
        for (i, item) in end.into_iter().enumerate() {
            alloc_box[S + gap_size + i].write(item);
        }

        let ptr = NonNull::from(alloc_box);
        Self {
            start: NonNull::slice_from_raw_parts(ptr.cast::<T>(), S),
            end: NonNull::slice_from_raw_parts(
                // SAFETY: we have initialized E items starting from S + gap_size
                // We cannot remove this unsafe without miri complaining due to both not being from
                // the same pointer.
                unsafe { ptr.cast::<T>().add(S + gap_size) },
                E,
            ),
        }
    }

    /// Initialize a [`RawGapBuf`] by byte copying from the source.
    ///
    /// Useful when reallocating the buffer.
    #[inline]
    pub fn new_with_slice(start: &[&[T]], gap_size: usize, end: &[&[T]]) -> Self
    where
        T: Copy,
    {
        let start_len = start.iter().map(|s| s.len()).sum();
        let end_len = end.iter().map(|s| s.len()).sum();
        let total_len: usize = start_len + end_len + gap_size;

        if Self::IS_ZST || total_len == 0 {
            let dangling = NonNull::dangling();
            return Self {
                start: NonNull::slice_from_raw_parts(dangling, start_len),
                end: NonNull::slice_from_raw_parts(dangling, end_len),
            };
        }

        let alloc_ptr = Box::leak(Box::<[T]>::new_uninit_slice(total_len));

        let mut i = 0;
        let mut offset = 0;

        while i < start.len() {
            for val in start[i].iter().copied() {
                alloc_ptr[offset].write(val);
                offset += 1;
            }

            i += 1;
        }

        offset += gap_size;

        i = 0;
        while i < end.len() {
            for val in end[i].iter().copied() {
                alloc_ptr[offset].write(val);
                offset += 1;
            }
            i += 1;
        }
        Self {
            start: NonNull::slice_from_raw_parts(
                NonNull::from(&mut *alloc_ptr).cast::<T>(),
                start_len,
            ),
            end: NonNull::slice_from_raw_parts(
                NonNull::from(&alloc_ptr[start_len + gap_size..]).cast::<T>(),
                end_len,
            ),
        }
    }

    #[inline(always)]
    pub const fn get_parts(&self) -> [&[T]; 2] {
        let (start, _, end) = self.as_slices();
        [start, end]
    }

    #[inline(always)]
    pub const fn get_parts_mut(&mut self) -> [&mut [T]; 2] {
        let (start, _, end) = self.as_slices_mut();
        [start, end]
    }

    pub const fn as_slices(&self) -> (&[T], &[MaybeUninit<T>], &[T]) {
        unsafe {
            let start = self.start().as_ref();
            let gap = NonNull::slice_from_raw_parts(
                self.start_ptr()
                    .cast::<MaybeUninit<T>>()
                    .add(self.start_len()),
                self.gap_len(),
            )
            .as_ref();
            let end = self.end().as_ref();
            (start, gap, end)
        }
    }

    pub const fn as_slices_mut(&mut self) -> (&mut [T], &mut [MaybeUninit<T>], &mut [T]) {
        unsafe {
            let start = self.start().as_mut();
            let gap = NonNull::slice_from_raw_parts(
                self.start_ptr()
                    .cast::<MaybeUninit<T>>()
                    .add(self.start_len()),
                self.gap_len(),
            )
            .as_mut();
            let end = self.end().as_mut();
            (start, gap, end)
        }
    }

    #[inline(always)]
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len() {
            return None;
        }
        let [start, end] = self.get_parts();
        if index >= start.len() {
            Some(&end[index - start.len()])
        } else {
            Some(&start[index])
        }
    }

    #[inline(always)]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index >= self.len() {
            return None;
        }
        let [start, end] = self.get_parts_mut();
        if index >= start.len() {
            Some(&mut end[index - start.len()])
        } else {
            Some(&mut start[index])
        }
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
    pub fn get_slice(&mut self, r: Range<usize>) -> Option<&mut [T]> {
        let r = get_range(self.len(), r)?;
        self.move_gap_out_of(r.start..r.end);
        debug_assert!(is_get_single(self.start_len(), r.start, r.end));
        let start_len = self.start_len();
        let [start, end] = self.get_parts_mut();
        if r.start >= start_len {
            Some(&mut end[r.start - start_len..r.len()])
        } else {
            Some(&mut start[r.start..r.end])
        }
    }

    #[inline(always)]
    pub fn get_range(&self, r: Range<usize>) -> Option<[&[T]; 2]> {
        let len = self.len();
        let r = get_range(len, r)?;

        if is_get_single(self.start_len(), r.start, r.end) {
            let [start, end] = self.get_parts();
            if r.start >= self.start_len() {
                let start_len = self.start_len();
                return Some([&[], &end[r.start - start_len..r.end - start_len]]);
            } else {
                return Some([&start[r.start..r.end], &[]]);
            }
        }

        let [start, end] = self.get_parts();
        Some([&start[r.start..], &end[0..r.end - self.start_len()]])
    }

    #[inline(always)]
    pub fn get_range_mut(&mut self, r: Range<usize>) -> Option<[&mut [T]; 2]> {
        let len = self.len();
        let r = get_range(len, r)?;

        let start_len = self.start_len();
        let [start, end] = self.get_parts_mut();
        if is_get_single(start_len, r.start, r.end) {
            if r.start >= start_len {
                return Some([&mut [], &mut end[r.start - start_len..r.end - start_len]]);
            } else {
                return Some([&mut start[r.start..r.end], &mut []]);
            }
        }

        Some([&mut start[r.start..], &mut end[0..r.end - start_len]])
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
    pub const fn spare_capacity_ptr(&mut self) -> NonNull<[MaybeUninit<T>]> {
        unsafe {
            let gap_start = self.start.cast::<MaybeUninit<T>>().add(self.start.len());
            let gap_len = self.gap_len();
            NonNull::slice_from_raw_parts(gap_start, gap_len)
        }
    }

    /// Returns a pointer to the possibly uninitialized gap
    ///
    /// This function explicity returns a pointer instead of a `&mut [T]` to allow specialized
    /// implementations (such as a string buffer) to do efficient copying without worrying about
    /// drop code.
    #[inline(always)]
    pub const fn spare_capacity_mut(&mut self) -> &mut [MaybeUninit<T>] {
        unsafe { self.spare_capacity_ptr().as_mut() }
    }

    /// Returns the current gap length
    #[inline(always)]
    pub const fn gap_len(&self) -> usize {
        // with ZST's there is no gap length, as such the subtraction below can overflow
        if Self::IS_ZST {
            return isize::MAX as usize - self.start_len() + self.end_len();
        }
        unsafe { self.end_ptr().offset_from(self.start_ptr()) as usize - self.start_len() }
    }

    /// Returns the length of the total allocation
    #[inline(always)]
    pub const fn total_len(&self) -> usize {
        let len = self.len();
        // with ZST's the gap length is usize::MAX, just return the number of items since we will
        // not allocate anyway
        if Self::IS_ZST {
            return len;
        }

        len + self.gap_len()
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
            assert!(
                t_ptr.add(start_len + by) <= self.end_ptr(),
                "cannot grow that start value as it overlaps with the end slice"
            );
        }
        self.start = NonNull::slice_from_raw_parts(t_ptr, start_len + by);
    }

    /// Grow the start slice with the provided value
    #[inline(always)]
    pub fn grow_start_with(&mut self, val: T) {
        if self.gap_len() == 0 {
            self.grow_gap(1);
        }

        self.spare_capacity_mut()[0].write(val);
        unsafe {
            self.grow_start(1);
        };
    }

    /// Grow the start slice with the provided value
    #[inline(always)]
    pub fn grow_start_with_slice(&mut self, val: &[T])
    where
        T: Copy,
    {
        if self.gap_len() < val.len() {
            self.grow_gap(val.len());
        }

        let spare = self.spare_capacity_mut();
        for (i, val) in val.iter().copied().enumerate() {
            spare[i].write(val);
        }

        unsafe {
            self.grow_start(val.len());
        };
    }

    /// Shrink the start slice by the provided value
    ///
    /// Returns the shrunken portion of the start slice as a pointer.
    /// Caller must deal with T's drop code. To avoid memory leaks.
    ///
    /// # Panics
    ///
    /// Start length should always be greater than or equal to the argument.
    #[inline(always)]
    pub fn shrink_start(&mut self, by: usize) -> NonNull<[T]> {
        let start_len = self.start_len();
        assert!(by <= start_len);
        self.start = NonNull::slice_from_raw_parts(self.start_ptr(), start_len - by);
        NonNull::slice_from_raw_parts(self.spare_capacity_ptr().cast::<T>(), by)
    }

    /// Shrink the start slice by the provided value
    ///
    /// Returns the shrunken portion of the start slice.
    ///
    /// # Panics
    ///
    /// Start length should always be greater than or equal to the argument.
    #[inline(always)]
    pub fn shrink_start_with(&mut self, by: usize) -> &mut [T]
    where
        T: Copy,
    {
        let start_len = self.start_len();
        assert!(by <= start_len);

        unsafe { self.shrink_start(by).as_mut() }
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
            assert!(
                self.gap_len() >= by,
                "cannot grow the end slice when the grow overlaps with the start slice"
            );
        }
        let t_ptr = unsafe { self.end_ptr().sub(by) };
        self.end = NonNull::slice_from_raw_parts(t_ptr, end_len + by);
    }

    /// Shrink the end slice by the provided value
    ///
    /// # Safety
    /// Caller must ensure that the values are correctly dropped, the end length >= by, and that
    /// the pointer has enough provenance.
    #[inline(always)]
    pub unsafe fn shrink_end(&mut self, by: usize) -> NonNull<[T]> {
        let end_len = self.end_len();

        // ensure shrinking the slice does not point out of bounds
        assert!(
            end_len >= by,
            "cannot shrink start slice when shrink value is more than the total length"
        );
        let old_end = self.end_ptr();
        let t_ptr = unsafe { self.end_ptr().add(by) };
        self.end = NonNull::slice_from_raw_parts(t_ptr, end_len - by);
        NonNull::slice_from_raw_parts(old_end, by)
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
        unsafe {
            self.start = NonNull::slice_from_raw_parts(
                self.start_ptr(),
                self.start_len().checked_add_signed(by).unwrap_unchecked(),
            );
            self.end = NonNull::slice_from_raw_parts(
                self.end_ptr().offset(by),
                self.end_len().checked_add_signed(-by).unwrap_unchecked(),
            );
        }
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

        if Self::IS_ZST {
            // SAFETY: for ZST's we don't have to actually move anything around
            // the result of the logic below is pointless so just shift the gap
            unsafe { self.shift_gap(self.start_len() as isize - (to as isize)) };
            return;
        }

        // this code is pretty ugly, but results in pretty clean assembly with relatively little
        // branching
        //
        // TODO: should benchmark if this is even worth it
        let start_len = self.start_len();
        let (start, spare, end) = self.as_slices_mut();
        let gap_len = spare.len();
        let shift: isize;
        // a tagged scope is used to reduce the branch count
        // the shift operation always happens, but src and dst cannot be overlapping
        // if they are overlapping exit the scope after copying, and just shift the slices.
        'ov: {
            let src;
            let dst;
            let copy_count;
            // move gap left
            if to < start_len && start_len - to <= gap_len {
                copy_count = start_len - to;
                shift = -(copy_count as isize);
                src = NonNull::from(&start[start_len - copy_count..]).cast::<T>();
                dst = NonNull::from(&mut spare[gap_len - copy_count..]).cast::<MaybeUninit<T>>();
            }
            // move gap right
            else if to > start_len && to - start_len <= gap_len {
                copy_count = to - start_len;
                src = NonNull::from(&end[0..copy_count]).cast::<T>();
                dst = NonNull::from(&mut spare[0..copy_count]).cast::<MaybeUninit<T>>();
                shift = copy_count as isize;
            } else {
                // move gap right
                let (src, dst, copy_count) = if to >= self.start_len() {
                    copy_count = to - self.start_len();
                    shift = copy_count as isize;

                    (
                        self.end_ptr(),
                        self.spare_capacity_ptr().cast::<MaybeUninit<T>>(),
                        copy_count,
                    )
                }
                // move gap left
                else {
                    copy_count = self.start_len() - to;
                    shift = -(copy_count as isize);
                    unsafe {
                        (
                            self.start_ptr().add(to),
                            self.start_ptr().add(to + gap_len).cast::<MaybeUninit<T>>(),
                            copy_count,
                        )
                    }
                };

                let src = src.cast::<MaybeUninit<T>>();

                unsafe { src.copy_to(dst, copy_count) };
                // the copy is not non overlapping so we did it right above
                // skip the copy call right below and just shift the gap
                break 'ov;
            }

            let src = src.cast::<MaybeUninit<T>>();
            // debug assertion in case there is a logic error above
            assert!(
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
    #[inline(always)]
    pub fn move_gap_out_of(&mut self, r: Range<usize>) {
        assert!(self.total_len() >= r.end && r.start <= r.end);
        if r.start > self.start_len() || r.end <= self.start_len() {
            return;
        }

        // determine the minimum copies needed to move the gap out of the range
        let to_right_copy = self.start_len() - r.start;
        let to_left_copy = r.end - self.start_len();
        let move_to = if to_right_copy > to_left_copy {
            r.end
        } else {
            r.start
        };
        self.move_gap_start_to(move_to);
    }

    /// Drop's Self, calling the drop code of the stored T
    #[cfg(test)]
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
        if Self::IS_ZST {
            return;
        }
        unsafe {
            self.start.drop_in_place();
            self.end.drop_in_place();
        }
    }

    /// Reallocate the buffer with the provided gap size
    ///
    /// Generally [`RawGapBuf::grow_gap_at`] should be preferred instead as in most cases of
    /// reallocation, the goal is to allocate enough space to before an insertion is performed.
    ///
    /// This is allows growing or shrinking the gap without any knowledge of the insertions size
    /// (such as an iterator of T's).
    pub(crate) fn grow_gap(&mut self, by: usize) {
        let [start, _] = self.get_parts();
        self.grow_gap_at(by, start.len());
    }

    /// Reallocate the buffer and position the gap start at the provided position
    pub(crate) fn grow_gap_at(&mut self, by: usize, at: usize) {
        assert!(self.len() >= at);
        if Self::IS_ZST {
            // fake the gap grow
            *self = Self {
                start: NonNull::slice_from_raw_parts(NonNull::dangling(), at),
                end: NonNull::slice_from_raw_parts(NonNull::dangling(), self.len() - at),
            };
            return;
        }

        let start_len = self.start_len();
        let gap_len = self.gap_len();
        let end_len = self.end_len();
        let mut v = unsafe {
            Box::from_raw(
                NonNull::slice_from_raw_parts(
                    self.start_ptr_mut().cast::<MaybeUninit<T>>(),
                    self.total_len(),
                )
                .as_ptr(),
            )
        }
        .into_vec();

        v.reserve_exact(by);
        unsafe { v.set_len(start_len + gap_len + end_len + by) };

        let b = v.into_boxed_slice();
        let start_ptr: NonNull<T> = NonNull::from(Box::leak(b)).cast::<T>();
        let old_end = unsafe { start_ptr.add(start_len + gap_len) };
        let end_ptr: NonNull<T> = unsafe { old_end.add(by) };
        unsafe { old_end.copy_to(end_ptr, end_len) };

        self.start = NonNull::slice_from_raw_parts(start_ptr, start_len);
        self.end = NonNull::slice_from_raw_parts(end_ptr, end_len);
        self.move_gap_start_to(at);
    }

    pub fn shrink_gap(&mut self, by: usize) {
        if Self::IS_ZST || by == 0 {
            return;
        }

        let gap_len = self.gap_len();

        assert!(gap_len >= by);
        let start_len = self.start_len();
        let end_len = self.end_len();
        let total_len = start_len + gap_len + end_len;

        unsafe {
            let gap_ptr = self.start_ptr().add(self.start_len() + gap_len - by);

            // SAFETY: both are valid for enough read and writes
            self.end_ptr().copy_to(gap_ptr, self.end_len());

            let b = Box::from_raw(
                NonNull::slice_from_raw_parts(
                    self.start_ptr_mut().cast::<MaybeUninit<T>>(),
                    total_len,
                )
                .as_ptr(),
            );

            let mut v = b.into_vec();

            // SAFETY: we are storing uninits in it anyway
            v.set_len(total_len - by);

            let buf = Box::leak(v.into_boxed_slice());

            let new_ptr = NonNull::from(buf).cast::<T>();

            self.start = NonNull::slice_from_raw_parts(new_ptr, start_len);
            self.end =
                NonNull::slice_from_raw_parts(new_ptr.add(start_len + gap_len - by), end_len);
        }
    }
}

impl<T> Clone for RawGapBuf<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let start_len = self.start_len();
        let gap_len = self.gap_len();
        let end_len = self.end_len();
        let mut alloc_box = Box::<[T]>::new_uninit_slice(self.total_len());
        let [start, end] = self.get_parts();
        for (i, item) in start.iter().enumerate() {
            alloc_box[i].write(item.clone());
        }

        let end_slice = &mut alloc_box[start_len + gap_len..];
        for (i, item) in end.iter().enumerate() {
            end_slice[i].write(item.clone());
        }
        let end_ptr = NonNull::from(&mut *end_slice).cast::<T>();

        let leaked = NonNull::from(Box::leak(alloc_box)).cast::<T>();
        Self {
            start: NonNull::slice_from_raw_parts(leaked, start_len),
            end: NonNull::slice_from_raw_parts(end_ptr, end_len),
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
            drop(Box::<[MaybeUninit<T>]>::from_raw(
                NonNull::slice_from_raw_parts(
                    self.start_ptr().cast::<MaybeUninit<T>>(),
                    self.total_len(),
                )
                .as_ptr(),
            ));
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
        let s_buf = RawGapBuf::new_with_slice(
            &[[1, 2, 3].as_slice(), [4, 5, 6].as_slice()],
            10,
            &[[7, 8, 9].as_slice(), [10, 11, 12].as_slice()],
        );
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
        assert_eq!(s_buf.get_range(5..5).unwrap(), [&[], &[]]);
        assert_eq!(s_buf.get_range(6..6), None);

        // get single item as slice
        assert_eq!(s_buf.get_range(3..4), Some([[].as_slice(), &[4]]));
        assert_eq!(s_buf.get_range(4..5), Some([[].as_slice(), &[5]]));
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

    #[test]
    fn grow_gap() {
        let mut s_buf = RawGapBuf::<String>::new();
        s_buf.grow_gap(20);
        assert_eq!(s_buf.gap_len(), 20);
        assert!(s_buf.is_empty());
        unsafe {
            s_buf.start_ptr().write(String::from("Hi"));
            s_buf.grow_start(1);
            s_buf.end_ptr().sub(1).write(String::from("Bye"));
            s_buf.grow_end(1);
        };

        assert_eq!(s_buf.get_parts(), [&["Hi"], ["Bye"].as_slice()]);

        s_buf.grow_gap(10);
        assert_eq!(s_buf.get_parts(), [&["Hi"], ["Bye"].as_slice()]);

        s_buf.grow_gap(20);
        assert_eq!(s_buf.get_parts(), [&["Hi"], ["Bye"].as_slice()]);

        s_buf.grow_gap(0);
        assert_eq!(s_buf.get_parts(), [&["Hi"], ["Bye"].as_slice()]);

        s_buf.grow_gap(30);
        assert_eq!(s_buf.get_parts(), [&["Hi"], ["Bye"].as_slice()]);

        s_buf.drop_in_place();
    }

    #[test]
    fn shrink_gap() {
        let mut s_buf = RawGapBuf::<String>::new();
        s_buf.grow_gap(20);
        assert_eq!(s_buf.gap_len(), 20);
        assert!(s_buf.is_empty());
        unsafe {
            s_buf.start_ptr().write(String::from("Hi"));
            s_buf.grow_start(1);
            s_buf.end_ptr().sub(1).write(String::from("Bye"));
            s_buf.grow_end(1);
        };

        s_buf.shrink_gap(10);

        assert_eq!(s_buf.gap_len(), 8);
        assert_eq!(s_buf.get_parts(), [&["Hi"], ["Bye"].as_slice()]);

        s_buf.drop_in_place();

        let mut s_buf = RawGapBuf::<String>::new();
        s_buf.grow_gap(20);
        assert_eq!(s_buf.gap_len(), 20);
        assert!(s_buf.is_empty());
        unsafe {
            s_buf.start_ptr().write(String::from("Hi"));
            s_buf.grow_start(1);
            s_buf.end_ptr().sub(1).write(String::from("Bye"));
            s_buf.grow_end(1);
        };

        s_buf.shrink_gap(18);

        assert_eq!(s_buf.gap_len(), 0);
        assert_eq!(s_buf.get_parts(), [&["Hi"], ["Bye"].as_slice()]);

        s_buf.drop_in_place();
    }

    #[test]
    #[should_panic]
    fn shrink_gap_panics() {
        let mut s_buf = RawGapBuf::<String>::new();
        s_buf.grow_gap(20);
        assert_eq!(s_buf.gap_len(), 20);
        assert!(s_buf.is_empty());
        unsafe {
            s_buf.start_ptr().write(String::from("Hi"));
            s_buf.grow_start(1);
            s_buf.end_ptr().sub(1).write(String::from("Bye"));
            s_buf.grow_end(1);
        };

        // in order to run this with miri we need to drop the T before the panic to avoid a memory
        // leak
        unsafe { s_buf.drop_t() };
        s_buf.shrink_gap(19);
    }
}
