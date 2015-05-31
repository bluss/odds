use std::{slice, mem};

/// Safe to use with any wholly initialized memory `ptr`
pub unsafe fn raw_byte_repr<'a, T>(ptr: &'a T) -> &'a [u8] {
    slice::from_raw_parts(
        ptr as *const _ as *const u8,
        mem::size_of::<T>(),
    )
}
