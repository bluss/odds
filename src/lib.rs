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
pub mod string;

pub use fix::Fix;
pub use range::IndexRange;
use unreachable::unreachable;

use std::{slice, mem};

/// Compare if **a** and **b** are equal *as pointers*.
#[inline]
pub fn ref_eq<T>(a: &T, b: &T) -> bool {
    ptr_eq(a, b)
}

/// Compare if **a** and **b** are equal pointers.
#[inline]
pub fn ptr_eq<T>(a: *const T, b: *const T) -> bool {
    a == b
}

/// Safe to use with any wholly initialized memory `ptr`
#[inline]
pub unsafe fn raw_byte_repr<T: ?Sized>(ptr: &T) -> &[u8] {
    slice::from_raw_parts(
        ptr as *const _ as *const u8,
        mem::size_of_val(ptr),
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

/// Check slicing bounds in debug mode, otherwise just act as an unchecked
/// slice call.
#[inline]
pub unsafe fn slice_unchecked<T>(data: &[T], from: usize, to: usize) -> &[T] {
    debug_assert!((&data[from..to], true).1);
    std::slice::from_raw_parts(data.as_ptr().offset(from as isize), to - from)
}

#[test]
fn test_repr() {
    unsafe {
        assert_eq!(raw_byte_repr(&17u8), &[17]);
        assert_eq!(raw_byte_repr("abc"), "abc".as_bytes());
    }
}

#[test]
#[should_panic]
fn test_get_unchecked_1() {
    if cfg!(not(debug_assertions)) {
        panic!();
    }
    unsafe {
        get_unchecked(&[1, 2, 3], 3);
    }
}

#[test]
#[should_panic]
fn test_slice_unchecked_1() {
    // These tests only work in debug mode
    if cfg!(not(debug_assertions)) {
        panic!();
    }
    unsafe {
        slice_unchecked(&[1, 2, 3], 0, 4);
    }
}

#[test]
#[should_panic]
fn test_slice_unchecked_2() {
    if cfg!(not(debug_assertions)) {
        panic!();
    }
    unsafe {
        slice_unchecked(&[1, 2, 3], 4, 4);
    }
}

#[test]
fn test_slice_unchecked_3() {
    // This test only works in release mode
    // test some benign unchecked slicing
    let data = [1, 2, 3, 4];
    let sl = &data[0..0];
    if cfg!(debug_assertions) {
        /* silent */
    } else {
        unsafe {
            assert_eq!(slice_unchecked(sl, 0, 4), &[1, 2, 3, 4]);
        }
    }
}
