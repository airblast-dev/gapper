use std::{marker::PhantomData, ops::RangeBounds, ptr::NonNull};

use crate::{
    grower::Grower,
    raw_gap_buf::RawGapBuf,
    utils::{get_parts_at, get_range},
};

use super::drain::Drain;

#[derive(Clone)]
struct GrowingGapBuf<T, G: Grower<[T]>> {
    raw: RawGapBuf<T>,
    grower: G,
}

impl<T, G: Grower<[T]>> GrowingGapBuf<T, G> {
    #[inline(always)]
    pub fn new() -> GrowingGapBuf<T, G>
    where
        G: Default,
    {
        Self {
            raw: RawGapBuf::default(),
            grower: G::default(),
        }
    }

    #[inline(always)]
    pub fn with_grower(grower: G) -> Self {
        Self {
            raw: Default::default(),
            grower,
        }
    }

    #[inline(always)]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.raw.get(index)
    }

    #[inline(always)]
    pub fn get_slice<RB: RangeBounds<usize>>(&self, r: RB) -> Option<[&[T]; 2]> {
        let r = get_range(self.raw.len(), r)?;
        self.raw.get_slice(r)
    }

    #[inline(always)]
    #[allow(clippy::wrong_self_convention)]
    pub fn to_slice(&mut self) -> &[T] {
        self.raw.to_slice()
    }

    #[inline(always)]
    pub fn to_slice_mut(&mut self) -> &mut [T] {
        self.raw.to_slice_mut()
    }

    #[inline]
    pub fn insert(&mut self, at: usize, val: T) {
        assert!(self.raw.get(at).is_some() || self.raw.len() == at);
        if self.raw.gap_len() == 0 {
            let [start, end] = self.raw.get_parts();
            let base = self.grower.base_gap_size(start, end);
            let max = self.grower.max_gap_size(start, end);
            self.realloc(base.min(max) + 1);
        }
        self.raw.move_gap_start_to(at);
        unsafe {
            self.raw.spare_capacity_mut().cast::<T>().write(val);
            self.raw.grow_start(1);
        }
    }

    #[inline(always)]
    pub fn drain<RB: RangeBounds<usize>>(&mut self, r: RB) -> Option<Drain<'_, T>> {
        let r = get_range(self.raw.len(), r)?;
        self.raw.move_gap_start_to(r.end);
        let ret = Some(Drain {
            ptr: unsafe {
                NonNull::slice_from_raw_parts(self.raw.start_ptr().add(r.start), r.len())
            },
            __p: PhantomData,
        });

        unsafe { self.raw.shrink_start(r.len()) };

        ret
    }

    pub(crate) fn realloc(&mut self, gap_size: usize) {
        let [start, end] = self.raw.get_parts();
        let new = unsafe { RawGapBuf::new_with_slice(&[start], gap_size, &[end]) };
        drop(core::mem::replace(&mut self.raw, new));
    }

    pub(crate) fn realloc_gap_at(&mut self, gap_size: usize, at: usize) {
        let [start, end] = self.raw.get_parts();
        let temp;
        let temp2;
        let (left, right) = {
            let (start, mid, end, before_mid) = get_parts_at(start, end, at);
            if before_mid {
                temp2 = [mid, end];
                temp = [start];
                (temp.as_slice(), temp2.as_slice())
            } else {
                temp2 = [start, mid];
                temp = [end];
                (temp2.as_slice(), temp.as_slice())
            }
        };
        let new = unsafe { RawGapBuf::new_with_slice(left, gap_size, right) };
        drop(core::mem::replace(&mut self.raw, new));
    }
}

impl<T, G: Grower<[T]>> Drop for GrowingGapBuf<T, G> {
    fn drop(&mut self) {
        unsafe { self.raw.drop_t() };
    }
}

#[cfg(test)]
mod tests {
    use crate::grower::DefaultGrower;

    use super::GrowingGapBuf;

    type GapBuf = GrowingGapBuf<String, DefaultGrower>;

    #[test]
    fn insert() {
        let mut s_buf = GapBuf::new();

        s_buf.insert(0, String::from("Hi"));
        assert_eq!(s_buf.get(0).map(String::as_str), Some("Hi"));
        assert_eq!(s_buf.get(1).map(String::as_str), None);
        assert_eq!(s_buf.get(2).map(String::as_str), None);

        s_buf.insert(0, String::from("Bye"));
        assert_eq!(s_buf.get(0).map(String::as_str), Some("Bye"));
        assert_eq!(s_buf.get(1).map(String::as_str), Some("Hi"));
        assert_eq!(s_buf.get(2).map(String::as_str), None);
        assert_eq!(s_buf.get(3).map(String::as_str), None);

        s_buf.insert(2, String::from("World"));
        assert_eq!(s_buf.get(0).map(String::as_str), Some("Bye"));
        assert_eq!(s_buf.get(1).map(String::as_str), Some("Hi"));
        assert_eq!(s_buf.get(2).map(String::as_str), Some("World"));
        assert_eq!(s_buf.get(3).map(String::as_str), None);
        assert_eq!(s_buf.get(4).map(String::as_str), None);
    }

    #[test]
    fn drain() {
        let mut s_buf = GapBuf::new();
        for (i, val) in ["1", "2", "3"].map(String::from).into_iter().enumerate() {
            s_buf.insert(i, val);
        }
        let sample = s_buf.clone();

        let drain = s_buf.drain(0..2).unwrap();
        assert_eq!(drain.as_slice(), &["1", "2"]);
        drop(drain);
        assert_eq!(s_buf.get(0).unwrap(), "3");
        assert_eq!(s_buf.get(1), None);
        assert_eq!(s_buf.get(2), None);
        assert_eq!(s_buf.to_slice(), &["3"]);

        let drain = s_buf.drain(0..0).unwrap();
        assert_eq!(drain.as_slice(), ([] as [String; 0]).as_slice());

        let mut s_buf = sample.clone();
        let drain = s_buf.drain(0..3).unwrap();
        let v = Vec::from_iter(drain);
        assert_eq!(v, &["1", "2", "3"]);
        s_buf.insert(0, String::from("4"));
        assert_eq!(s_buf.get(0).unwrap(), "4");
        assert_eq!(s_buf.get(1), None);
        assert_eq!(s_buf.get(2), None);
        assert_eq!(s_buf.to_slice(), &["4"]);
    }

    #[test]
    #[allow(clippy::iter_nth_zero)]
    fn drain_iter() {
        let mut s_buf = GapBuf::new();
        for (i, val) in ["1", "2", "3", "4"]
            .map(String::from)
            .into_iter()
            .enumerate()
        {
            s_buf.insert(i, val);
        }
        let sample = s_buf.clone();

        let mut drain_iter = s_buf.drain(0..4).unwrap();
        assert_eq!(drain_iter.next_back().unwrap(), "4");
        assert_eq!(drain_iter.next_back().unwrap(), "3");
        assert_eq!(drain_iter.next().unwrap(), "1");
        assert_eq!(drain_iter.next().unwrap(), "2");
        assert!(drain_iter.next().is_none());
        assert!(drain_iter.next_back().is_none());

        let mut s_buf = sample.clone();
        let mut drain_iter = s_buf.drain(1..4).unwrap();
        assert_eq!(drain_iter.nth(1).unwrap(), "3");
        assert_eq!(drain_iter.nth(0).unwrap(), "4");
        assert_eq!(drain_iter.nth(0), None);
        assert_eq!(drain_iter.nth(1), None);
        assert_eq!(drain_iter.nth(2), None);

        let mut s_buf = sample.clone();
        let drain_iter = s_buf.drain(0..4).unwrap();
        assert_eq!(drain_iter.count(), 4)
    }
}
