#[derive(Clone, Copy, Debug)]
pub enum GapSlice<'a> {
    Spaced(&'a str, &'a str),
    Single(&'a str),
}
