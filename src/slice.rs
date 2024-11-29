#[derive(Clone, Copy, Debug)]
enum GapSlice<'a> {
    Spaced(&'a str, &'a str),
    Single(&'a str),
}
