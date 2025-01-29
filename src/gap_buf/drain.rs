use std::{iter::FusedIterator, marker::PhantomData, ptr::NonNull};

pub struct Drain<'a, T> {
    // The value lives as long as 'a, but we are able to safely mutate the values as it is now
    // added to the gap. As long as the gap buffer this originated from is not mutated this is safe
    // to use in any way.
    ptr: NonNull<[T]>,
    __p: PhantomData<&'a T>,
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
        if len == 0 {
            return None;
        }
        n = n.min(len);
        let ptr = self.ptr.cast::<T>();
        let t = unsafe { ptr.read() };
        self.ptr = NonNull::slice_from_raw_parts(unsafe { ptr.add(n) }, len - n);
        Some(t)
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
