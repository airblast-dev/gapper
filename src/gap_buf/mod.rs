use crate::grower::DefaultGrower;

mod buf;
mod drain;

pub use buf::GrowingGapBuf;
pub use drain::Drain;
pub type GapBuf<T> = GrowingGapBuf<T, DefaultGrower>;
