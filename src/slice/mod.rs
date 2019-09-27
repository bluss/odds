//! Extra functions for slices

pub mod blocked;
pub mod iter;
pub mod unalign;
pub mod rev;

pub use self::rev::RevSlice;

use std::ptr;
use std::cmp::min;
use std::mem::{self, align_of, size_of};
use std::slice::from_raw_parts;

use rawslice::SliceIter;
use unchecked_index::get_unchecked;

/// Unaligned load of a u64 at index `i` in `buf`
unsafe fn load_u64(buf: &[u8], i: usize) -> u64 {
    debug_assert!(i + 8 <= buf.len());
    let mut data = 0u64;
    ptr::copy_nonoverlapping(get_unchecked(buf, i), &mut data as *mut _ as *mut u8, 8);
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

/// Rotate `steps` towards lower indices.
///
/// The steps to rotate is computed modulo the length of `data`,
/// so any step value is acceptable. This function does not panic.
///
/// ```
/// use odds::slice::rotate_left;
///
/// let mut data = [1, 2, 3, 4];
/// rotate_left(&mut data, 1);
/// assert_eq!(&data, &[2, 3, 4, 1]);
/// rotate_left(&mut data, 2);
/// assert_eq!(&data, &[4, 1, 2, 3]);
/// ```
pub fn rotate_left<T>(data: &mut [T], steps: usize) {
    //return rotate_alt(data, steps);
    // no bounds checks in this method in this version
    if data.len() == 0 {
        return;
    }
    let steps = steps % data.len();

    data[..steps].reverse();
    data[steps..].reverse();
    data.reverse();
}

#[test]
fn test_shared_prefix() {
    let mut a = [0xff; 256];
    let b = [0xff; 256];
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

/// Element-finding methods for slices
pub trait SliceFind {
    type Item;
    /// Linear search for the first occurrence  `elt` in the slice.
    ///
    /// Return its index if it is found, or None.
    fn find<U: ?Sized>(&self, elt: &U) -> Option<usize>
        where Self::Item: PartialEq<U>;

    /// Linear search for the last occurrence  `elt` in the slice.
    ///
    /// Return its index if it is found, or None.
    fn rfind<U: ?Sized>(&self, elt: &U) -> Option<usize>
        where Self::Item: PartialEq<U>;
}

impl<T> SliceFind for [T] { 
    type Item = T;
    fn find<U: ?Sized>(&self, elt: &U) -> Option<usize>
        where Self::Item: PartialEq<U>
    {
        SliceIter::from(self).position(move |x| *x == *elt)
    }

    fn rfind<U: ?Sized>(&self, elt: &U) -> Option<usize>
        where Self::Item: PartialEq<U>
    {
        SliceIter::from(self).rposition(move |x| *x == *elt)
    }
}

/// Element-finding methods for slices
pub trait SliceFindSplit {
    type Item;
    /// Linear search for the first occurrence  `elt` in the slice.
    ///
    /// Return the part before and the part including and after the element.
    /// If the element is not found, the second half is empty.
    fn find_split<U: ?Sized>(&self, elt: &U) -> (&Self, &Self)
        where Self::Item: PartialEq<U>;

    /// Linear search for the last occurrence  `elt` in the slice.
    ///
    /// Return the part before and the part including and after the element.
    /// If the element is not found, the first half is empty.
    fn rfind_split<U: ?Sized>(&self, elt: &U) -> (&Self, &Self)
        where Self::Item: PartialEq<U>;

    /// Linear search for the first occurrence  `elt` in the slice.
    ///
    /// Return the part before and the part including and after the element.
    /// If the element is not found, the second half is empty.
    fn find_split_mut<U: ?Sized>(&mut self, elt: &U) -> (&mut Self, &mut Self)
        where Self::Item: PartialEq<U>;

    /// Linear search for the last occurrence  `elt` in the slice.
    ///
    /// Return the part before and the part including and after the element.
    /// If the element is not found, the first half is empty.
    fn rfind_split_mut<U: ?Sized>(&mut self, elt: &U) -> (&mut Self, &mut Self)
        where Self::Item: PartialEq<U>;
}


/// Unchecked version of `xs.split_at(i)`.
unsafe fn split_at_unchecked<T>(xs: &[T], i: usize) -> (&[T], &[T]) {
    (get_unchecked(xs, ..i),
     get_unchecked(xs, i..))
}

impl<T> SliceFindSplit for [T] { 
    type Item = T;
    fn find_split<U: ?Sized>(&self, elt: &U) -> (&Self, &Self)
        where Self::Item: PartialEq<U>
    {
        let i = self.find(elt).unwrap_or(self.len());
        unsafe {
            split_at_unchecked(self, i)
        }
    }

    fn find_split_mut<U: ?Sized>(&mut self, elt: &U) -> (&mut Self, &mut Self)
        where Self::Item: PartialEq<U>
    {
        let i = self.find(elt).unwrap_or(self.len());
        self.split_at_mut(i)
    }

    fn rfind_split<U: ?Sized>(&self, elt: &U) -> (&Self, &Self)
        where Self::Item: PartialEq<U>
    {
        let i = self.rfind(elt).unwrap_or(0);
        unsafe {
            split_at_unchecked(self, i)
        }
    }

    fn rfind_split_mut<U: ?Sized>(&mut self, elt: &U) -> (&mut Self, &mut Self)
        where Self::Item: PartialEq<U>
    {
        let i = self.rfind(elt).unwrap_or(0);
        self.split_at_mut(i)
    }
}


/// "plain old data": Types that we can stick arbitrary bit patterns into,
/// and thus use them as blocks in `split_aligned_for` or in `UnalignedIter`.
pub unsafe trait Pod : Copy { }
macro_rules! impl_pod {
    (@array $($e:expr),+) => {
        $(
        unsafe impl<T> Pod for [T; $e] where T: Pod { }
        )+
    };
    ($($t:ty)+) => {
        $(
        unsafe impl Pod for $t { }
        )+
    };
}
impl_pod!{u8 u16 u32 u64 usize i8 i16 i32 i64 isize}
impl_pod!{@array 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}


/// Split the input slice into three chunks,
/// so that the middle chunk is a slice of a larger "block size"
/// (for example T could be u64) that is correctly aligned for `T`.
///
/// The first and last returned slices are the remaining head and tail
/// parts that could not be baked into `&[T]`
///
/// # Examples
///
/// ```
/// extern crate odds;
/// use odds::slice::split_aligned_for;
///
/// fn count_ones(data: &[u8]) -> u32 {
///     let mut total = 0;
///     let (head, mid, tail) = split_aligned_for::<[u64; 2]>(data);
///     total += head.iter().map(|x| x.count_ones()).sum::<u32>();
///     total += mid.iter().map(|x| x[0].count_ones() + x[1].count_ones()).sum::<u32>();
///     total += tail.iter().map(|x| x.count_ones()).sum::<u32>();
///     total
/// }
///
/// fn main() {
///     assert_eq!(count_ones(&vec![3u8; 127]), 127 * 2);
/// }
/// ```
pub fn split_aligned_for<T: Pod>(data: &[u8]) -> (&[u8], &[T], &[u8]) {
    let ptr = data.as_ptr();
    let align_t = align_of::<T>();
    let size_t = size_of::<T>();
    let align_ptr = ptr as usize & (align_t - 1);
    let prefix = if align_ptr == 0 { 0 } else { align_t - align_ptr };
    let t_len;

    if prefix > data.len() {
        t_len = 0;
    } else {
        t_len = (data.len() - prefix) / size_t;
    }
    unsafe {
        (from_raw_parts(ptr, prefix),
         from_raw_parts(ptr.offset(prefix as isize) as *const T, t_len),
         from_raw_parts(ptr.offset((prefix + t_len * size_t) as isize),
                        data.len() - t_len * size_t - prefix))
    }
}

#[cfg(feature = "std")]
#[test]
fn test_split_aligned() {
    let data = vec![0; 1024];
    assert_eq!(data.as_ptr() as usize & 7, 0);
    let (a, b, c) = split_aligned_for::<u8>(&data);
    assert_eq!(a.len(), 0);
    assert_eq!(b.len(), data.len());
    assert_eq!(c.len(), 0);

    let (a, b, c) = split_aligned_for::<u64>(&data);
    assert_eq!(a.len(), 0);
    assert_eq!(b.len(), data.len() / 8);
    assert_eq!(c.len(), 0);

    let offset1 = &data[1..data.len() - 2];
    let (a, b, c) = split_aligned_for::<u64>(offset1);
    assert_eq!(a.len(), 7);
    assert_eq!(b.len(), data.len() / 8 - 2);
    assert_eq!(c.len(), 6);

    let data = [0; 7];
    let (a, b, c) = split_aligned_for::<u64>(&data);
    assert_eq!(a.len() + c.len(), 7);
    assert_eq!(b.len(), 0);
}


/* All of these use this trick:
 *
    for i in 0..4 {
        if i < data.len() {
            f(&data[i]);
        }
    }
 * The intention is that the range makes sure the compiler
 * sees that the loop is not autovectorized or something that generates
 * a lot of code in vain that does not pay off when it's only 3 elements or less.
 */

#[cfg(test)]
pub fn unroll_2<'a, T, F>(data: &'a [T], mut f: F)
    where F: FnMut(&'a T)
{
    let mut data = data;
    while data.len() >= 2 {
        f(&data[0]);
        f(&data[1]);
        data = &data[2..];
    }
    // tail
    if 0 < data.len() {
        f(&data[0]);
    }
}
#[cfg(test)]
pub fn unroll_4<'a, T, F>(data: &'a [T], mut f: F)
    where F: FnMut(&'a T)
{
    let mut data = data;
    while data.len() >= 4 {
        f(&data[0]);
        f(&data[1]);
        f(&data[2]);
        f(&data[3]);
        data = &data[4..];
    }
    // tail
    for i in 0..3 {
        if i < data.len() {
            f(&data[i]);
        }
    }
}

#[cfg(test)]
pub fn unroll_8<'a, T, F>(data: &'a [T], mut f: F)
    where F: FnMut(&'a T)
{
    let mut data = data;
    while data.len() >= 8 {
        f(&data[0]);
        f(&data[1]);
        f(&data[2]);
        f(&data[3]);
        f(&data[4]);
        f(&data[5]);
        f(&data[6]);
        f(&data[7]);
        data = &data[8..];
    }
    // tail
    for i in 0..7 {
        if i < data.len() {
            f(&data[i]);
        }
    }
}

#[cfg(test)]
pub fn zip_unroll_4<'a, 'b, A, B, F>(a: &'a [A], b: &'b [B], mut f: F)
    where F: FnMut(usize, &'a A, &'b B)
{
    let len = min(a.len(), b.len());
    let mut a = &a[..len];
    let mut b = &b[..len];
    while a.len() >= 4 {
        f(0, &a[0], &b[0]);
        f(1, &a[1], &b[1]);
        f(2, &a[2], &b[2]);
        f(3, &a[3], &b[3]);
        a = &a[4..];
        b = &b[4..];
    }
    // tail
    for i in 0..3 {
        if i < a.len() {
            f(0, &a[i], &b[i]);
        }
    }
}

#[cfg(test)]
pub fn zip_unroll_8<'a, 'b, A, B, F>(a: &'a [A], b: &'b [B], mut f: F)
    where F: FnMut(usize, &'a A, &'b B)
{
    let len = min(a.len(), b.len());
    let mut a = &a[..len];
    let mut b = &b[..len];
    while a.len() >= 8 {
        f(0, &a[0], &b[0]);
        f(1, &a[1], &b[1]);
        f(2, &a[2], &b[2]);
        f(3, &a[3], &b[3]);
        f(4, &a[4], &b[4]);
        f(5, &a[5], &b[5]);
        f(6, &a[6], &b[6]);
        f(7, &a[7], &b[7]);
        a = &a[8..];
        b = &b[8..];
    }

    // tail
    for i in 0..7 {
        if i < a.len() {
            f(0, &a[i], &b[i]);
        }
    }
}

#[cfg(test)]
pub fn f64_dot(xs: &[f64], ys: &[f64]) -> f64 {
    let mut sum = [0.; 8];
    zip_unroll_8(xs, ys, |i, x, y| sum[i] += x * y);
    sum[0] += sum[4];
    sum[1] += sum[5];
    sum[2] += sum[6];
    sum[3] += sum[7];
    sum[0] += sum[2];
    sum[1] += sum[3];
    sum[0] + sum[1]
}

#[test]
fn test_find() {
    let v = [0, 1, 7, 0, 0, 2, 3, 5, 1, 5, 3, 1, 2, 1];
    assert_eq!(v.find_split(&7), v.split_at(2));
    assert_eq!(v.rfind_split(&7), v.split_at(2));
    assert_eq!(v.rfind_split(&2), v.split_at(v.len() - 2));
}

