use std::{iter::FusedIterator, marker::PhantomData, ptr::NonNull};

#[derive(Debug)]
pub struct Drain<'a, T> {
    // The value lives as long as 'a, but we are able to safely mutate the values as it is now
    // added to the gap. As long as the gap buffer this originated from is not mutated this is safe
    // to use in any way.
    pub(crate) ptr: NonNull<[T]>,
    pub(crate) __p: PhantomData<&'a T>,
}

impl<T> Drain<'_, T> {
    #[inline(always)]
    pub fn as_slice(&self) -> &[T] {
        unsafe { self.ptr.as_ref() }
    }

    #[inline(always)]
    pub fn as_slice_mut(&mut self) -> &mut [T] {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let len = self.ptr.len();
        if len == 0 {
            return None;
        }
        let ptr = self.ptr.cast::<T>();
        let t = unsafe { ptr.read() };
        self.ptr = NonNull::slice_from_raw_parts(unsafe { ptr.add(1) }, len - 1);
        Some(t)
    }

    fn nth(&mut self, mut n: usize) -> Option<Self::Item>
    where
        Self: Sized,
    {
        let len = self.ptr.len();
        if n >= len {
            return None;
        }
        let ptr = self.ptr.cast::<T>();

        // go to the requested value and read it
        let t = unsafe { ptr.add(n).read() };
        // drop all values until the one that was read
        unsafe { NonNull::slice_from_raw_parts(ptr, n).drop_in_place() };

        // we minimally always drop one value in this branch
        // to account for the item that was read, and the ones that were dropped readjust the slice
        // start and length
        n += 1;
        self.ptr = NonNull::slice_from_raw_parts(unsafe { ptr.add(n) }, len - n);
        Some(t)
    }

    fn count(mut self) -> usize
        where
            Self: Sized, {
        let len = self.ptr.len();
        // drop the items and set the length as the count method should exhaust all items
        // we also have to leave the fields in valid state in case [`Iterator::by_ref`] or
        // similar methods are used
        //
        // same as calling [`Iterator::next`] until None is returned
        unsafe { self.ptr.drop_in_place() };
        self.ptr = NonNull::slice_from_raw_parts(self.ptr.cast::<T>(), 0);
        len
    }

    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        let len = self.ptr.len();
        if len == 0 {
            return None;
        }

        let ptr = self.ptr.cast::<T>();
        let t = unsafe { ptr.add(len - 1).read() };
        self.ptr = NonNull::slice_from_raw_parts(ptr, len - 1);

        Some(t)
    }
}

impl<T> DoubleEndedIterator for Drain<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let len = self.ptr.len();
        if len == 0 {
            return None;
        }
        let ptr = self.ptr.cast::<T>();

        // we already checked if len is zero above, this cannot wrap
        let t = unsafe { ptr.add(len - 1).read() };
        self.ptr = NonNull::slice_from_raw_parts(ptr, len - 1);
        Some(t)
    }
}

impl<T> FusedIterator for Drain<'_, T> {}

impl<T> Drop for Drain<'_, T> {
    fn drop(&mut self) {
        unsafe {
            self.ptr.drop_in_place();
        }
    }
}

// see buf.rs module for drain tests
