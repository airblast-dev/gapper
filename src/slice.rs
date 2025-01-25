use std::fmt::Display;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GapSlice<'a>(pub &'a str, pub &'a str);

impl PartialEq<str> for GapSlice<'_> {
    fn eq(&self, other: &str) -> bool {
        other.get(..self.0.len()).is_some_and(|o1| o1 == self.0)
            && other.get(self.0.len()..).is_some_and(|o2| o2 == self.1)
    }
}

impl PartialEq<&str> for GapSlice<'_> {
    fn eq(&self, other: &&str) -> bool {
        self.eq(*other)
    }
}

impl Display for GapSlice<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.0, self.1)
    }
}
