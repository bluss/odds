use std::{slice, mem};

/// Safe to use with any wholly initialized memory `ptr`
pub unsafe fn raw_byte_repr<'a, T>(ptr: &'a T) -> &'a [u8] {
    slice::from_raw_parts(
        ptr as *const _ as *const u8,
        mem::size_of::<T>(),
    )
}

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
