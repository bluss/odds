//! Odds and ends — collection miscellania.
//!
//! - Utilities for debug-checked, release-unchecked indexing and slicing
//! - Fixpoint combinator for closures
//! - String and Vec extensions
//!
//! The **odds** crate has the following crate feature flags:
//!
//! - `std-vec`
//!   - Enable Vec extensions
//!   - Implies `std`
//! - `std-string`
//!   - Enable String extensions
//!   - Implies `std`
//! - `std`
//!   - Enable basic libstd usage.
//! - `unstable`.
//!   - Optional.
//!   - Requires nightly channel.
//!   - Implement the closure traits for **Fix**.
//!
//! If none of the std features are enabled (they are not enabled by default),
//! then the crate is `no_std`.
//!
//! # Rust Version
//!
//! This version of the crate requires Rust 1.15 or later.
//!

#![doc(html_root_url = "https://docs.rs/odds/0.4/")]
#![cfg_attr(feature="unstable", feature(unboxed_closures, fn_traits))]

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate core as std;
extern crate rawslice;
extern crate rawpointer;
extern crate unchecked_index;

mod range;
#[path = "fix.rs"]
mod fix_impl;
pub mod char;
pub mod string;
pub mod vec;
pub mod slice;
pub mod stride;

pub use crate::fix_impl::Fix;
pub use crate::fix_impl::fix;
pub use crate::range::IndexRange;

use crate::std::mem;

/// prelude of often used traits and functions
pub mod prelude {
    pub use crate::slice::SliceFind;
    pub use crate::string::StrExt;
    pub use crate::string::StrChunksWindows;
    #[cfg(feature = "std-string")]
    pub use string::StringExt;
    #[cfg(feature = "std-vec")]
    pub use vec::{vec, VecExt};
    #[doc(no_inline)]
    pub use crate::IndexRange;
    #[doc(no_inline)]
    pub use crate::fix;
}

/// Safe to use with any wholly initialized memory `ptr`
#[inline]
pub unsafe fn raw_byte_repr<T: ?Sized>(ptr: &T) -> &[u8] {
    std::slice::from_raw_parts(
        ptr as *const _ as *const u8,
        mem::size_of_val(ptr),
    )
}

#[inline(always)]
unsafe fn unreachable() -> ! {
    enum Void { }
    match *(1 as *const Void) {
        /* unreachable */
    }
}

/// Act as `debug_assert!` in debug mode, asserting that this point is not reached.
///
/// In release mode, no checks are done, and it acts like the `unreachable` intrinsic.
#[inline(always)]
pub unsafe fn debug_assert_unreachable() -> ! {
    debug_assert!(false, "Entered unreachable section, this is a bug!");
    unreachable()
}

/// Create a length 1 slice out of a reference
pub fn ref_slice<T>(ptr: &T) -> &[T] {
    unsafe {
        std::slice::from_raw_parts(ptr, 1)
    }
}

/// Create a length 1 mutable slice out of a reference
pub fn ref_slice_mut<T>(ptr: &mut T) -> &mut [T] {
    unsafe {
        std::slice::from_raw_parts_mut(ptr, 1)
    }
}


#[test]
fn test_repr() {
    unsafe {
        assert_eq!(raw_byte_repr(&17u8), &[17]);
        assert_eq!(raw_byte_repr("abc"), "abc".as_bytes());
    }
}
