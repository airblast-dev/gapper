#[cold]
#[track_caller]
#[inline(never)]
pub(crate) fn position_not_on_char_boundry(pos: usize) -> ! {
    panic!("provided position ({pos}) must always lie on a char boundry");
}
#[cold]
#[track_caller]
#[inline(never)]
pub(crate) fn oob_read() -> ! {
    panic!("index for gap insertion is out of bounds");
}
