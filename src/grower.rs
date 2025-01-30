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
