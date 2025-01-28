use std::{mem::MaybeUninit, num::NonZeroUsize, ptr::NonNull};

pub(crate) struct RawGapBuf<T> {
    /// Using NonNull for Null pointer optimization
    start: NonNull<[T]>,
    end: NonNull<[T]>,
}

// compile time assertion to ensure that RawGapBuf is null pointer optimized
const _: () = assert!(
    core::mem::size_of::<RawGapBuf<NonZeroUsize>>()
        == core::mem::size_of::<Option<RawGapBuf<NonZeroUsize>>>()
);

impl<T> RawGapBuf<T> {
    #[inline]
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

    #[inline(always)]
    pub const fn get_slices(&self) -> (&[T], &[T]) {
        unsafe { (self.start.as_ref(), self.end.as_ref()) }
    }

    #[inline(always)]
    pub const fn get_slices_mut(&mut self) -> (&mut [T], &mut [T]) {
        unsafe { (self.start.as_mut(), self.end.as_mut()) }
    }

    #[inline(always)]
    pub const fn start_ptr(&self) -> NonNull<[T]> {
        self.start
    }

    #[inline(always)]
    pub const fn start_ptr_mut(&mut self) -> NonNull<[T]> {
        self.start
    }

    #[inline(always)]
    pub const fn end_ptr(&self) -> NonNull<[T]> {
        self.end
    }

    #[inline(always)]
    pub const fn end_ptr_mut(&mut self) -> NonNull<[T]> {
        self.end
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

    #[inline(always)]
    pub const fn gap_len(&self) -> usize {
        unsafe {
            self.end_ptr()
                .cast::<T>()
                .offset_from(self.start_ptr().cast::<T>()) as usize
                - self.start_ptr().len()
        }
    }

    #[inline(always)]
    pub const fn total_len(&self) -> usize {
        unsafe {
            (self.end.cast::<T>().offset_from(self.start.cast::<T>()) as usize)
                + self.end_ptr().len()
        }
    }

    /// Grow the start slice by the provided value
    ///
    /// # Safety
    /// Caller must ensure that the values are initialized, and that growing the start does not
    /// cause overlapping with the end.
    #[inline(always)]
    pub unsafe fn grow_start(&mut self, by: usize) {
        let start_len = self.start_ptr().len();
        let t_ptr = self.start.cast::<T>();

        // ensure extending the start does not cause an overlap with the end pointer
        debug_assert!(
            start_len + by
                < self
                    .end_ptr()
                    .cast::<T>()
                    .offset_from(self.start_ptr().cast::<T>()) as usize,
            "cannot grow that start value as it overlaps with the end slice"
        );
        self.start = NonNull::slice_from_raw_parts(t_ptr, start_len + by);
    }

    /// Shrink the start slice by the provided value
    ///
    /// # Safety
    /// Caller must ensure that the values are correctly dropped, the start length >= by, and that
    /// the pointer has enough provenance.
    #[inline(always)]
    pub unsafe fn shrink_start(&mut self, by: usize) {
        let start_len = self.start_ptr().len();

        // ensure shrinking the slice does not point out of bounds
        debug_assert!(
            start_len >= by,
            "cannot shrink start slice when shrink value is more than the total length"
        );
        let t_ptr = self.start.cast::<T>();
        self.start = NonNull::slice_from_raw_parts(t_ptr, start_len - by);
    }

    /// Grow the end slice by the provided value
    ///
    /// # Safety
    /// Caller must ensure that the values before the end pointer are initialized, does not
    /// overlap with the start slice and that the pointer has enough provenance.
    #[inline(always)]
    pub unsafe fn grow_end(&mut self, by: usize) {
        let end_len = self.end_ptr().len();
        debug_assert!(
            self.gap_len() >= by,
            "cannot grow the end slice when the grow overlaps with the start slice"
        );
        let t_ptr = self.end.cast::<T>().sub(by);
        self.end = NonNull::slice_from_raw_parts(t_ptr, end_len + by);
    }

    /// Shrink the end slice by the provided value
    ///
    /// # Safety
    /// Caller must ensure that the values are correctly dropped, the end length >= by, and that
    /// the pointer has enough provenance.
    #[inline(always)]
    pub unsafe fn shrink_end(&mut self, by: usize) {
        let end_len = self.end_ptr().len();

        // ensure shrinking the slice does not point out of bounds
        debug_assert!(
            end_len >= by,
            "cannot shrink start slice when shrink value is more than the total length"
        );
        let t_ptr = unsafe { self.start.cast::<T>().add(by) };
        self.end = NonNull::slice_from_raw_parts(t_ptr, end_len - by);
    }
}

// This implementation allows us to cover every single From implementation for a boxed slice
impl<T> Clone for RawGapBuf<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        let start_len = self.start_ptr().len();
        let gap_len = self.gap_len();
        let end_len = self.end_ptr().len();
        let buf: Box<[MaybeUninit<T>]> = Box::new_uninit_slice(start_len + gap_len + end_len);
        unsafe {
            let leaked = NonNull::new_unchecked(Box::leak(buf).as_mut_ptr());
            let (start, end) = self.get_slices();
            for (i, item) in start.iter().enumerate() {
                leaked.add(i).write(MaybeUninit::new(item.clone()));
            }

            let end_start = leaked.add(start_len + gap_len);

            for (i, item) in end.iter().enumerate() {
                end_start.add(i).write(MaybeUninit::new(item.clone()));
            }

            Self {
                start: NonNull::slice_from_raw_parts(leaked.cast::<T>(), start_len),
                end: NonNull::slice_from_raw_parts(end_start.cast::<T>(), end_len),
            }
        }
    }
}

impl<T, A> From<A> for RawGapBuf<T>
where
    Box<[T]>: From<A>,
{
    fn from(value: A) -> Self {
        let buf: Box<[T]> = Box::from(value);
        let val_len = buf.len();

        // The box will be dropped manually as part of RawGapBuf's drop implementation
        let start_ptr = unsafe { NonNull::new_unchecked(Box::leak(buf).as_mut_ptr()) };

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

    // to be able to run the tests (practically) with miri we need to avoid leaking any resources
    impl<T> RawGapBuf<T> {
        fn drop_inner(self) {
            unsafe {
                self.start.drop_in_place();
                self.end.drop_in_place();
            }
        }
    }

    #[test]
    fn new() {
        let s_buf: RawGapBuf<String> = RawGapBuf::new();
        assert_eq!(s_buf.start_ptr(), s_buf.end_ptr());
        assert_eq!(s_buf.start_ptr(), s_buf.end_ptr());
    }

    #[test]
    fn get_slice() {
        let s_buf: RawGapBuf<String> = RawGapBuf::new();
        let (start, end) = s_buf.get_slices();
        assert!(start.is_empty());
        assert!(end.is_empty());
    }

    #[test]
    fn get_slice_mut() {
        let mut s_buf: RawGapBuf<String> = RawGapBuf::new();
        let (start, end) = s_buf.get_slices_mut();
        assert!(start.is_empty());
        assert!(end.is_empty());
    }

    #[test]
    fn gap_len() {
        let s_buf: RawGapBuf<String> = RawGapBuf::new();
        assert_eq!(s_buf.gap_len(), 0);
        let s_buf: RawGapBuf<String> = RawGapBuf::from(["Hello".to_string()].as_slice());
        assert_eq!(s_buf.gap_len(), 0);
        s_buf.drop_inner();
    }

    #[test]
    fn total_len() {
        let s_buf = RawGapBuf::from(["Hi"]);
        assert_eq!(1, s_buf.total_len());
    }

    #[test]
    fn from_slice() {
        let s_buf: RawGapBuf<String> = RawGapBuf::from(["Hello".to_string()].as_slice());
        s_buf.drop_inner();
    }

    #[test]
    fn from_box_slice() {
        let s_buf: RawGapBuf<String> = RawGapBuf::from(Box::from(["Hello".to_string()]));
        s_buf.drop_inner();
    }

    #[test]
    fn clone() {
        let s_buf: RawGapBuf<String> = RawGapBuf::from(["Hello".to_string(), "Bye".to_string()]);
        let cloned_s_buf = s_buf.clone();
        assert_eq!(s_buf.get_slices(), cloned_s_buf.get_slices());
        s_buf.drop_inner();
        cloned_s_buf.drop_inner();
    }
}
