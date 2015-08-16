
use std::ops::{
    RangeFull,
    RangeFrom,
    RangeTo,
    Range,
};

/// **IndexRange** is implemented by Rust's built-in range types, produced
/// by range syntax like `..`, `a..`, `..b` or `c..d`.
pub trait IndexRange {
    #[inline]
    /// Start index (inclusive)
    fn start(&self) -> Option<usize> { None }
    #[inline]
    /// End index (exclusive)
    fn end(&self) -> Option<usize> { None }
}


impl IndexRange for RangeFull {}

impl IndexRange for RangeFrom<usize> {
    #[inline]
    fn start(&self) -> Option<usize> { Some(self.start) }
}

impl IndexRange for RangeTo<usize> {
    #[inline]
    fn end(&self) -> Option<usize> { Some(self.end) }
}

impl IndexRange for Range<usize> {
    #[inline]
    fn start(&self) -> Option<usize> { Some(self.start) }
    #[inline]
    fn end(&self) -> Option<usize> { Some(self.end) }
}

