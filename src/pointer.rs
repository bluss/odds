//! Raw pointer extensions

use std::mem::size_of;

/// Return the number of elements of `T` from `start` to `end`.<br>
/// Return the arithmetic difference if `T` is zero size.
#[inline(always)]
pub fn ptrdistance<T>(start: *const T, end: *const T) -> usize {
    let size = size_of::<T>();
    if size == 0 {
        (end as usize).wrapping_sub(start as usize)
    } else {
        (end as usize - start as usize) / size
    }
}

