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

#[cold]
#[track_caller]
#[inline(never)]
pub(crate) fn invalid_offset(len: usize, src_offset: usize, dst_offset: usize, copy_count: usize) -> ! {
    panic!(
        "pointers should never overlap when copying, \
                len is {}, source pointer offset is {}, destination \
                pointer offset is {} with a copy count of {}",
        len, src_offset, dst_offset, copy_count
    );
}
