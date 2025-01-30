pub trait Grower<T: ?Sized> {
    fn base_gap_size(&mut self, start: &T, end: &T) -> usize;
    fn max_gap_size(&mut self, start: &T, end: &T) -> usize;
}

#[derive(Clone, Copy, Default, Debug)]
pub struct DefaultGrower;
impl<T> Grower<[T]> for DefaultGrower {
    #[inline(always)]
    fn base_gap_size(&mut self, _: &[T], _: &[T]) -> usize {
        4096
    }

    #[inline(always)]
    fn max_gap_size(&mut self, start: &[T], end: &[T]) -> usize {
        ((start.len() + end.len()) / 100 * 5).max(self.base_gap_size(start, end))
    }
}

impl Grower<str> for DefaultGrower {
    #[inline(always)]
    fn base_gap_size(&mut self, start: &str, end: &str) -> usize {
        self.base_gap_size(start.as_bytes(), end.as_bytes())
    }

    #[inline(always)]
    fn max_gap_size(&mut self, start: &str, end: &str) -> usize {
        self.max_gap_size(start.as_bytes(), end.as_bytes())
    }
}

#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct TinyGrower;
impl<T: ?Sized> Grower<T> for TinyGrower {
    fn base_gap_size(&mut self, _: &T, _: &T) -> usize {
        1
    }

    fn max_gap_size(&mut self, _: &T, _: &T) -> usize {
        1
    }
}

#[cfg(test)]
#[derive(Clone, Copy, Debug)]
pub(crate) enum TestGrower {
    Default(DefaultGrower),
    TinyGrower(TinyGrower),
}

#[cfg(test)]
impl TestGrower {
    pub(crate) const ALL: [Self; 2] = [Self::Default(DefaultGrower), Self::TinyGrower(TinyGrower)];
}

#[cfg(test)]
impl<T> Grower<[T]> for TestGrower {
    fn max_gap_size(&mut self, start: &[T], end: &[T]) -> usize {
        match self {
            Self::Default(d) => d.max_gap_size(start, end),
            Self::TinyGrower(t) => t.max_gap_size(start, end),
        }
    }

    fn base_gap_size(&mut self, start: &[T], end: &[T]) -> usize {
        match self {
            Self::Default(d) => d.base_gap_size(start, end),
            Self::TinyGrower(t) => t.base_gap_size(start, end),
        }
    }
}

#[cfg(test)]
impl Grower<str> for TestGrower {
    fn max_gap_size(&mut self, start: &str, end: &str) -> usize {
        match self {
            Self::Default(d) => d.max_gap_size(start, end),
            Self::TinyGrower(t) => t.max_gap_size(start, end),
        }
    }

    fn base_gap_size(&mut self, start: &str, end: &str) -> usize {
        match self {
            Self::Default(d) => d.base_gap_size(start, end),
            Self::TinyGrower(t) => t.base_gap_size(start, end),
        }
    }
}
