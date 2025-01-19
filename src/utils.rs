#[inline(always)]
pub(crate) fn u8_is_char_boundry(u: u8) -> bool {
    const CHAR_BOUNDRY_MASK: u8 = 192;
    u < 0x80 || u & CHAR_BOUNDRY_MASK == CHAR_BOUNDRY_MASK
}
