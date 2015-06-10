//! Odds and ends — collection miscellania.
//!
//! The goal of this crate is to abolish itself. Things that are here
//! will move to other places when possible.
//!
//! The **odds** crate has the following cargo feature flags:
//!
//! - `unstable`.
//!   - Optional.
//!   - Requires nightly channel.
//!   - Implement the closure traits for **Fix**.
//!

#![cfg_attr(feature="unstable", feature(unboxed_closures, core))]

extern crate unreachable;

mod range;
mod fix;

pub use fix::Fix;
pub use range::IndexRange;
use unreachable::unreachable;

use std::{slice, mem};

/// Safe to use with any wholly initialized memory `ptr`
pub unsafe fn raw_byte_repr<'a, T>(ptr: &'a T) -> &'a [u8] {
    slice::from_raw_parts(
        ptr as *const _ as *const u8,
        mem::size_of::<T>(),
    )
}

/// Use `debug_assert!` to check indexing in debug mode. In release mode, no checks are done.
#[inline]
pub unsafe fn get_unchecked<T>(data: &[T], index: usize) -> &T {
    debug_assert!(index < data.len());
    data.get_unchecked(index)
}

/// Use `debug_assert!` to check indexing in debug mode. In release mode, no checks are done.
#[inline]
pub unsafe fn get_unchecked_mut<T>(data: &mut [T], index: usize) -> &mut T {
    debug_assert!(index < data.len());
    data.get_unchecked_mut(index)
}

/// Act as `debug_assert!` in debug mode, asserting that this point is not reached.
///
/// In release mode, no checks are done, and it acts like the `unreachable` intrinsic.
#[inline]
pub unsafe fn debug_assert_unreachable() -> ! {
    debug_assert!(false, "Entered unreachable section, this is a bug!");
    unreachable()
}
