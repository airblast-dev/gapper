use buf::GrowingGapBuf;

use crate::grower::DefaultGrower;

mod buf;
mod drain;

pub type GapBuf<T> = GrowingGapBuf<T, DefaultGrower>;
