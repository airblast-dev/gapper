use std::fmt::Display;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GapSlice<'a> {
    Spaced(&'a str, &'a str),
    Single(&'a str),
}

impl PartialEq<str> for GapSlice<'_> {
    fn eq(&self, other: &str) -> bool {
        let (s1, s2) = match self {
            Self::Single(s) => return *s == other,
            Self::Spaced(s1, s2) => (s1, s2),
        };
        other.get(..s1.len()).is_some_and(|o1| o1 == *s1)
            && other.get(s1.len()..).is_some_and(|o2| o2 == *s2)
    }
}

impl PartialEq<&str> for GapSlice<'_> {
    fn eq(&self, other: &&str) -> bool {
        self.eq(*other)
    }
}

impl Display for GapSlice<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (s1, s2) = match self {
            Self::Single(s) => (*s, ""),
            Self::Spaced(s1, s2) => (*s1, *s2)
        };
        write!(f, "{s1}{s2}")
    }
}
