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

#[cfg(test)]
pub(crate) mod test_utils {
    use rstest_reuse::template;

    pub(crate) use super::{DefaultGrower, Grower};

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

    #[derive(Clone, Copy, Debug, Default)]
    pub(crate) struct FuzzyGrower;

    impl<T: ?Sized> Grower<T> for FuzzyGrower {
        fn base_gap_size(&mut self, _: &T, _: &T) -> usize {
            rand::random::<u8>() as usize
        }

        fn max_gap_size(&mut self, _: &T, _: &T) -> usize {
            rand::random::<u8>() as usize
        }
    }

    #[derive(Clone, Copy, Debug)]
    pub(crate) enum TestGrower {
        Default(DefaultGrower),
        Tiny(TinyGrower),
        Fuzzy(FuzzyGrower),
    }

    impl<T> Grower<[T]> for TestGrower {
        fn max_gap_size(&mut self, start: &[T], end: &[T]) -> usize {
            match self {
                Self::Default(d) => d.max_gap_size(start, end),
                Self::Tiny(t) => t.max_gap_size(start, end),
                Self::Fuzzy(f) => f.max_gap_size(start, end),
            }
        }

        fn base_gap_size(&mut self, start: &[T], end: &[T]) -> usize {
            match self {
                Self::Default(d) => d.base_gap_size(start, end),
                Self::Tiny(t) => t.base_gap_size(start, end),
                Self::Fuzzy(f) => f.base_gap_size(start, end),
            }
        }
    }

    impl Grower<str> for TestGrower {
        fn max_gap_size(&mut self, start: &str, end: &str) -> usize {
            match self {
                Self::Default(d) => d.max_gap_size(start, end),
                Self::Tiny(t) => t.max_gap_size(start, end),
                Self::Fuzzy(f) => f.max_gap_size(start, end),
            }
        }

        fn base_gap_size(&mut self, start: &str, end: &str) -> usize {
            match self {
                Self::Default(d) => d.base_gap_size(start, end),
                Self::Tiny(t) => t.base_gap_size(start, end),
                Self::Fuzzy(f) => f.base_gap_size(start, end),
            }
        }
    }

    #[template]
    #[rstest]
    #[case::default(TestGrower::Default(DefaultGrower))]
    #[case::tiny(TestGrower::Tiny(TinyGrower))]
    #[case::fuzzy(TestGrower::Fuzzy(FuzzyGrower))]
    pub fn grower_template(#[case] g: TestGrower) {}
}
