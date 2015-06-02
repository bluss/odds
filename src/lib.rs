//! Odds and ends — collection miscellania.
//!
//! The goal of this crate is to abolish itself. Things that are here
//! will move to other places when possible.
pub use range::IndexRange;
mod range;

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

/// Fixpoint combinator for rust closures, generalized over the return type.
///
/// The **Fix** only supports direct function call notation with the nightly channel.
///
/// ```
/// use odds::Fix;
///
/// let c = |f: Fix<i32, _>, x| if x == 0 { 1 } else { x * f.call(x - 1) };
/// let fact = Fix(&c);
/// println!("{:?}", fact.call(5));
///
/// let data = &[true, false];
/// let all_true = |f: Fix<_, _>, x| {
///     let x: &[_] = x;
///     x.len() == 0 || x[0] && f.call(&x[1..])
/// };
/// let all = Fix(&all_true);
/// assert_eq!(all.call(data), false);
/// ```
pub struct Fix<'a, T, R>(pub &'a Fn(Fix<T, R>, T) -> R);

impl<'a, T, R> Fix<'a, T, R> {
    pub fn call(&self, arg: T) -> R {
        let f = *self;
        f.0(f, arg)
    }
}

impl<'a, T, R> Clone for Fix<'a, T, R> {
    fn clone(&self) -> Self { *self }
}

impl<'a, T, R> Copy for Fix<'a, T, R> { }

/// An empty type
pub enum Void { }

/// FIXME: Replace with intrinsic when it's stable
#[inline]
unsafe fn unreachable() -> ! {
    let void: &Void = mem::transmute(&());
    match *void {
        // no cases
    }
}

/// Act as `debug_assert!` in debug mode, asserting that this point is not reached.
///
/// In release mode, no checks are done, and it acts like the `unreachable` intrinsic.
#[inline]
pub unsafe fn debug_assert_unreachable() -> ! {
    debug_assert!(false, "Entered unreachable section, this is a bug!");
    unreachable()
}
