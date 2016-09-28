//! Extra functions for slices

use std::ptr;
use std::cmp::min;
use std::mem;

/// Unaligned load of a u64 at index `i` in `buf`
unsafe fn load_u64(buf: &[u8], i: usize) -> u64 {
    debug_assert!(i + 8 <= buf.len());
    let mut data = 0u64;
    ptr::copy_nonoverlapping(buf.get_unchecked(i), &mut data as *mut _ as *mut u8, 8);
    data
}

/// Return the end index of the longest shared (equal) prefix of `a` and `b`.
pub fn shared_prefix(a: &[u8], b: &[u8]) -> usize {
    let len = min(a.len(), b.len());
    let mut a = &a[..len];
    let mut b = &b[..len];
    let mut offset = 0;
    while a.len() >= 16 {
        unsafe {
            let a0 = load_u64(a, 0);
            let a1 = load_u64(a, 8);
            let b0 = load_u64(b, 0);
            let b1 = load_u64(b, 8);
            let d0 = a0 ^ b0;
            let d1 = a1 ^ b1;
            if d0 ^ d1 != 0 {
            //if d0 != 0 || d1 != 0 {
                break;
            }
        }
        offset += 16;
        a = &a[16..];
        b = &b[16..];
    }
    for i in 0..a.len() {
        if a[i] != b[i] {
            return offset + i;
        }
    }
    len
}


#[test]
fn correct() {
    let mut a = [0xff; 1024];
    let b = [0xff; 1024];
    for byte in 0..255 { // don't test byte 255
        for i in 0..a.len() {
            a[i] = byte;
            let ans = shared_prefix(&a, &b);
            assert!(ans == i, "failed for index {} and byte {:x} (got ans={})",
                    i, byte, ans);
            a[i] = 0xff;
        }
    }
}


pub trait SliceIterExt : Iterator {
    /// Return an iterator adaptor that joins together adjacent slices if possible.
    ///
    /// Only implemented for iterators with slice or string slice elements.
    /// Only slices that are contiguous together can be joined.
    ///
    /// ```
    /// use odds::slice::SliceIterExt;
    ///
    /// // Split a string into a slice per letter, filter out whitespace,
    /// // and join into words again by mending adjacent slices.
    /// let text = String::from("Warning:  γ-radiation (ionizing)");
    /// let char_slices = text.char_indices()
    ///                       .map(|(index, ch)| &text[index..index + ch.len_utf8()]);
    /// let words = char_slices.filter(|s| !s.chars().any(char::is_whitespace))
    ///                        .mend_slices();
    ///
    /// assert!(words.eq(vec!["Warning:", "γ-radiation", "(ionizing)"]));
    /// ```
    fn mend_slices(self) -> MendSlices<Self>
        where Self: Sized,
              Self::Item: MendSlice
    {
        MendSlices::new(self)
    }
}

impl<I: ?Sized> SliceIterExt for I where I: Iterator { }

/// An iterator adaptor that glues together adjacent contiguous slices.
///
/// See [`.mend_slices()`](../trait.Itertools.html#method.mend_slices) for more information.
pub struct MendSlices<I>
    where I: Iterator
{
    last: Option<I::Item>,
    iter: I,
}

impl<I: Clone> Clone for MendSlices<I>
    where I: Iterator,
          I::Item: Clone
{
    fn clone(&self) -> Self {
        MendSlices {
            last: self.last.clone(),
            iter: self.iter.clone(),
        }
    }
}

impl<I> MendSlices<I>
    where I: Iterator
{
    /// Create a new `MendSlices`.
    pub fn new(mut iter: I) -> Self {
        MendSlices {
            last: iter.next(),
            iter: iter,
        }
    }
}

impl<I> Iterator for MendSlices<I>
    where I: Iterator,
          I::Item: MendSlice
{
    type Item = I::Item;

    fn next(&mut self) -> Option<I::Item> {
        // this fuses the iterator
        let mut last = match self.last.take() {
            None => return None,
            Some(x) => x,
        };
        for next in &mut self.iter {
            match MendSlice::mend(last, next) {
                Ok(joined) => last = joined,
                Err((last_, next_)) => {
                    self.last = Some(next_);
                    return Some(last_);
                }
            }
        }

        Some(last)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// A trait for items that can *maybe* be joined together.
pub trait MendSlice
{
    #[doc(hidden)]
    /// If the slices are contiguous, return them joined into one.
    fn mend(Self, Self) -> Result<Self, (Self, Self)>
        where Self: Sized;
}

impl<'a, T> MendSlice for &'a [T] {
    #[inline]
    fn mend(a: Self, b: Self) -> Result<Self, (Self, Self)> {
        unsafe {
            let a_end = a.as_ptr().offset(a.len() as isize);
            if a_end == b.as_ptr() {
                Ok(::std::slice::from_raw_parts(a.as_ptr(), a.len() + b.len()))
            } else {
                Err((a, b))
            }
        }
    }
}

impl<'a, T> MendSlice for &'a mut [T] {
    #[inline]
    fn mend(a: Self, b: Self) -> Result<Self, (Self, Self)> {
        unsafe {
            let a_end = a.as_ptr().offset(a.len() as isize);
            if a_end == b.as_ptr() {
                Ok(::std::slice::from_raw_parts_mut(a.as_mut_ptr(), a.len() + b.len()))
            } else {
                Err((a, b))
            }
        }
    }
}

impl<'a> MendSlice for &'a str {
    #[inline]
    fn mend(a: Self, b: Self) -> Result<Self, (Self, Self)> {
        unsafe { mem::transmute(MendSlice::mend(a.as_bytes(), b.as_bytes())) }
    }
}

