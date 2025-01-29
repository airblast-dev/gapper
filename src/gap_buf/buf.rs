use crate::raw_gap_buf::RawGapBuf;

#[derive(Clone)]
struct GapBuf<T> {
    raw: RawGapBuf<T>
}
