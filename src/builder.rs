use std::borrow::Cow;

use crate::{box_with_gap, panics::invalid_max_gap_size, GapText, DEFAULT_GAP_SIZE};

pub struct GapBufBuilder {
    base_gap_size: usize,
    max_gap_size: MaxGapSizer,
}

impl Default for GapBufBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl GapBufBuilder {
    pub const fn new() -> Self {
        Self {
            base_gap_size: DEFAULT_GAP_SIZE,
            max_gap_size: MaxGapSizer::Percentage(5),
        }
    }

    pub const fn base_gap_size(mut self, base_gap_size: usize) -> Self {
        self.base_gap_size = base_gap_size;
        self
    }

    pub const fn max_gap_size(mut self, mut max_gap_size: MaxGapSizer) -> Self {
        if !max_gap_size.try_make_valid() {
            invalid_max_gap_size();
        }
        self.max_gap_size = max_gap_size;
        self
    }

    /// Build [`GapText`] with the provided configuration
    ///
    /// If passed a [`String`], the spare capacity of the buffer is used to initialize the gap to
    /// avoid an extra copy. If you do not expect any modifications and would rather not allocate
    /// extra space, [`String::shrink_to_fit`] or similar methods can be used to set a specific gap
    /// size before calling this method.
    ///
    /// If passed a &[`str`], the base gap size is and compared to the max gap size. The smaller
    /// value is used as the initial gap size.
    ///
    /// In both cases the gap is guaranteed to be at the end.
    pub fn build<'a, S: Into<Cow<'a, str>>>(self, s: S) -> GapText {
        let s: Cow<'_, str> = s.into();
        let (buf, gap) = match s {
            Cow::Owned(s) => {
                let mut buf_vec = s.into_bytes();
                let vec_len = buf_vec.len();

                // When an owned string is passed it is likely that it has spare capacity, we can
                // reuse it as a gap buffer.
                let spare = buf_vec.spare_capacity_mut();
                let spare_len = spare.len();

                // SAFETY: MaybeUninit is not copy so it does not benefit from the specialized implementation.
                // In our case we definitely know that the values are not initialized or, are initialized
                // with no drop code.
                // We initialize the values and set the vec length manually for performance.
                unsafe {
                    spare.as_mut_ptr().write_bytes(0, spare.len());
                    buf_vec.set_len(vec_len + spare_len);
                }
                (buf_vec.into_boxed_slice(), vec_len..vec_len + spare_len)
            }

            Cow::Borrowed(s) => {
                let max_gap_size = self
                    .max_gap_size
                    .max_gap_size(self.base_gap_size, 0, s.len());
                let cur_base_gap = max_gap_size.min(self.base_gap_size);
                (
                    box_with_gap!(cur_base_gap, 1, s.as_bytes()),
                    s.len()..s.len() + cur_base_gap,
                )
            }
        };

        GapText {
            buf,
            gap,
            base_gap_size: self.base_gap_size,
            max_gap_size: self.max_gap_size,
        }
    }
}

struct State {
    max_gap_size: MaxGapSizer,
}

#[non_exhaustive]
#[derive(Clone, Copy, Debug)]
pub enum MaxGapSizer {
    Percentage(u8),
    Fixed(u32),
    Func(fn(usize, usize, usize) -> usize),
}

impl MaxGapSizer {
    #[inline]
    fn max_gap_size(&self, base_gap_len: usize, gap: usize, total_len: usize) -> usize {
        match self {
            Self::Fixed(f) => *f as usize,
            Self::Percentage(p) => {
                // calculate the percentage using floats for accuracy
                // since p is always lesser or equal to 100, the result can never exceed u32::MAX
                // making it safe to cast to a usize
                (f64::from(total_len.min(u32::MAX as usize) as u32) / 100.0_f64 * f64::from(*p))
                    .ceil() as usize
            }
            Self::Func(f) => (f)(base_gap_len, gap, total_len),
        }
    }
}

impl MaxGapSizer {
    #[inline(always)]
    const fn try_make_valid(&mut self) -> bool {
        if let Self::Percentage(ref mut p) = self {
            if *p > 100 {
                *p = 100;
            }
        }
        true
    }
}

impl Default for MaxGapSizer {
    #[inline(always)]
    fn default() -> Self {
        Self::Percentage(5)
    }
}
