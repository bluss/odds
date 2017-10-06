//! A reversed view of a slice.

use std::hash::{Hasher, Hash};
use std::mem::transmute;
use std::iter::Rev;
use std::slice::{Iter, IterMut};

use std::ops::{Index, IndexMut};

use {get_unchecked, get_unchecked_mut};
use IndexRange;
use {slice_unchecked, slice_unchecked_mut};

use super::SliceFind;

/// A reversed view of a slice.
///
/// The `RevSlice` is a random accessible range of elements;
/// it wraps a regular slice but presents the underlying elements in
/// reverse order.
///
/// # Example
/// ```
/// use odds::slice::RevSlice;
///
/// let mut data = [0; 8];
///
/// {
///     let mut rev = <&mut RevSlice<_>>::from(&mut data);
///     for (i, elt) in rev.iter_mut().enumerate() {
///         *elt = i;
///     }
///
///     assert_eq!(&rev[..4], &[0, 1, 2, 3][..]);
/// }
/// assert_eq!(&data, &[7, 6, 5, 4, 3, 2, 1, 0]);
/// ```
///
/// Not visible in rustdoc:
///
/// - A boxed slice can be reversed too:
///   `impl<T> From<Box<[T]>> for Box<RevSlice<T>>`.
#[derive(Debug, Eq)]
// FIXME: Should be repr(transparent) when stable
pub struct RevSlice<T>([T]);

impl<T> RevSlice<T> {
    /// Return the length of the slice.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    // arithmetic overflow checked in debug builds
    #[inline]
    fn raw_index_no_wrap(&self, i: usize) -> usize {
        self.len() - (1 + i)
    }

    /// Return the index into the underlying slice, if it's in bounds
    fn raw_index(&self, i: usize) -> Option<usize> {
        if i < self.len() {
            Some(self.raw_index_no_wrap(i))
        } else {
            None
        }
    }

    /// Get element at index `i`.
    ///
    /// See also indexing notation: `&foo[i]`.
    pub fn get(&self, i: usize) -> Option<&T> {
        unsafe {
            self.raw_index(i).map(move |ri| get_unchecked(&self.0, ri))
        }
    }

    /// Get element at index `i`.
    ///
    /// See also indexing notation: `&mut foo[i]`.
    pub fn get_mut(&mut self, i: usize) -> Option<&mut T> {
        unsafe {
            self.raw_index(i).map(move |ri| get_unchecked_mut(&mut self.0, ri))
        }
    }

    pub fn inner_ref(&self) -> &[T] {
        &self.0
    }

    pub fn inner_mut(&mut self) -> &mut [T] {
        &mut self.0
    }

    #[cfg(feature = "std")]
    pub fn into_boxed_slice(self: Box<Self>) -> Box<[T]> {
        unsafe {
            transmute(self)
        }
    }

    /// Return a by-reference iterator
    pub fn iter(&self) -> Rev<Iter<T>> {
        self.into_iter()
    }

    /// Return a by-mutable-reference iterator
    pub fn iter_mut(&mut self) -> Rev<IterMut<T>> {
        self.into_iter()
    }

    pub fn split_at(&self, i: usize) -> (&Self, &Self) {
        assert!(i <= self.len());
        let ri = self.len() - i;
        let (a, b) = self.0.split_at(ri);
        (<_>::from(b), <_>::from(a))
    }

    pub fn split_at_mut(&mut self, i: usize) -> (&mut Self, &mut Self) {
        assert!(i <= self.len());
        let ri = self.len() - i;
        let (a, b) = self.0.split_at_mut(ri);
        (<_>::from(b), <_>::from(a))
    }
}

impl<T, U> PartialEq<RevSlice<U>> for RevSlice<T>
    where T: PartialEq<U>,
{
    fn eq(&self, rhs: &RevSlice<U>) -> bool {
        self.0 == rhs.0
    }
}

/// `RevSlice` compares by logical element sequence.
impl<T, U> PartialEq<[U]> for RevSlice<T>
    where T: PartialEq<U>,
{
    fn eq(&self, rhs: &[U]) -> bool {
        if self.len() != rhs.len() {
            return false;
        }
        for (x, y) in self.into_iter().zip(rhs) {
            if x != y {
                return false;
            }
        }
        true
    }
}

impl<T> Hash for RevSlice<T>
    where T: Hash,
{
    fn hash<H: Hasher>(&self, h: &mut H) {
        // hash like a slice of the same logical sequence
        self.len().hash(h);
        for elt in self {
            elt.hash(h)
        }
    }
}

impl<'a, T, Slice: ?Sized> From<&'a Slice> for &'a RevSlice<T>
    where Slice: AsRef<[T]>
{
    fn from(slc: &'a Slice) -> Self {
        unsafe {
            &*(slc.as_ref() as *const _ as *const RevSlice<T>)
        }
    }
}

impl<'a, T, Slice: ?Sized> From<&'a mut Slice> for &'a mut RevSlice<T>
    where Slice: AsMut<[T]>
{
    fn from(slc: &'a mut Slice) -> Self {
        unsafe {
            &mut *(slc.as_mut() as *mut _ as *mut RevSlice<T>)
        }
    }
}

#[cfg(feature = "std")]
impl<T> From<Box<[T]>> for Box<RevSlice<T>> {
    fn from(slc: Box<[T]>) -> Self {
        unsafe {
            Box::from_raw(Box::into_raw(slc) as *mut _ as *mut _)
        }
    }
}

impl<T> Index<usize> for RevSlice<T> {
    type Output = T;
    fn index(&self, i: usize) -> &T {
        if let Some(x) = self.get(i) {
            x
        } else {
            panic!("Index {} is out of bounds for RevSlice of length {}", i, self.len());
        }
    }
}

impl<T> IndexMut<usize> for RevSlice<T> {
    fn index_mut(&mut self, i: usize) -> &mut T {
        let len = self.len();
        if let Some(x) = self.get_mut(i) {
            return x;
        } else {
            panic!("Index {} is out of bounds for RevSlice of length {}", i, len);
        }
    }
}

impl<'a, T> Default for &'a RevSlice<T> {
    fn default() -> Self {
        Self::from(&[])
    }
}

impl<'a, T> Default for &'a mut RevSlice<T> {
    fn default() -> Self {
        Self::from(&mut [])
    }
}

impl<T, R> Index<R> for RevSlice<T>
    where R: IndexRange,
{
    type Output = RevSlice<T>;
    fn index(&self, index: R) -> &RevSlice<T> {
        // [0 1 2 3 4]
        //  4 3 2 1 0
        // [       ] <- rev 1..5  is 0..4
        let start = index.start().unwrap_or(0);
        let end = index.end().unwrap_or(self.len());
        assert!(start <= end && end <= self.len());
        let end_r = self.len() - start;
        let start_r = self.len() - end;
        unsafe {
            <&RevSlice<_>>::from(slice_unchecked(&self.0, start_r, end_r))
        }
    }
}

impl<T, R> IndexMut<R> for RevSlice<T>
    where R: IndexRange,
{
    fn index_mut(&mut self, index: R) -> &mut RevSlice<T> {
        // [0 1 2 3 4]
        //  4 3 2 1 0
        // [       ] <- rev 1..5  is 0..4
        let start = index.start().unwrap_or(0);
        let end = index.end().unwrap_or(self.len());
        assert!(start <= end && end <= self.len());
        let end_r = self.len() - start;
        let start_r = self.len() - end;
        unsafe {
            <&mut RevSlice<_>>::from(slice_unchecked_mut(&mut self.0, start_r, end_r))
        }
    }
}

impl<'a, T> IntoIterator for &'a RevSlice<T> {
    type Item = &'a T;
    type IntoIter = Rev<Iter<'a, T>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().rev()
    }
}

impl<'a, T> IntoIterator for &'a mut RevSlice<T> {
    type Item = &'a mut T;
    type IntoIter = Rev<IterMut<'a, T>>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut().rev()
    }
}

impl<T> SliceFind for RevSlice<T> {
    type Item = T;
    fn find<U: ?Sized>(&self, elt: &U) -> Option<usize>
        where Self::Item: PartialEq<U>
    {
        self.0.rfind(elt).map(move |i| self.raw_index_no_wrap(i))
    }

    fn rfind<U: ?Sized>(&self, elt: &U) -> Option<usize>
        where Self::Item: PartialEq<U>
    {
        self.0.find(elt).map(move |i| self.raw_index_no_wrap(i))
    }
}

/// Extension trait -- gives the .rev() methods to slices and revslices
pub trait RevExt {
    type Output;
    /// Return a reversed version of the slice
    ///
    /// .rev() of a slice is a RevSlice, and .rev() of a RevSlice is a regular
    /// slice.
    fn rev(self) -> Self::Output;
}

impl<'a, T> RevExt for &'a [T] {
    type Output = &'a RevSlice<T>;
    fn rev(self) -> Self::Output {
        <_>::from(self)
    }
}

impl<'a, T> RevExt for &'a mut [T] {
    type Output = &'a mut RevSlice<T>;
    fn rev(self) -> Self::Output {
        <_>::from(self)
    }
}

impl<'a, T> RevExt for &'a RevSlice<T> {
    type Output = &'a [T];
    fn rev(self) -> Self::Output {
        unsafe {
            &*(self as *const _ as *const _)
        }
    }
}

impl<'a, T> RevExt for &'a mut RevSlice<T> {
    type Output = &'a mut [T];
    fn rev(self) -> Self::Output {
        unsafe {
            &mut *(self as *mut _ as *mut _)
        }
    }
}

#[test]
fn test_rev_slice_1() {
    let data = [1, 2, 3, 4];
    let rev = [4, 3, 2, 1];

    assert_eq!(<&RevSlice<_>>::from(&data[..]), &rev[..]);
    assert!(<&RevSlice<_>>::from(&data[..]) != &data[..]);
    let r = <&RevSlice<_>>::from(&data[..]);
    assert_eq!(r[0], rev[0]);
    assert_eq!(r[3], rev[3]);
}

#[should_panic]
#[test]
fn test_rev_slice_2() {
    let data = [1, 2, 3, 4];

    let r = <&RevSlice<_>>::from(&data[..]);
    r[4];
}

#[should_panic]
#[test]
fn test_rev_slice_3() {
    let data = [1, 2, 3, 4];

    let r = <&RevSlice<_>>::from(&data[..]);
    r[!0];
}

#[test]
fn test_rev_slice_slice() {
    let data = [1, 2, 3, 4];
    let rev = [4, 3, 2, 1];

    let r = <&RevSlice<_>>::from(&data[..]);
    
    for i in 0..r.len() {
        for j in i..r.len() {
            println!("{:?}, {:?}", &r[i..j], &rev[i..j]);
            assert_eq!(&r[i..j], &rev[i..j]);
        }
    }
}

#[test]
fn test_rev_slice_find() {
    let data = [1, 2, 3, 4];

    let r = <&RevSlice<_>>::from(&data[..]);
    
    for (i, elt) in r.into_iter().enumerate() {
        assert_eq!(r.find(elt), Some(i));
    }
    for (i, elt) in r.into_iter().enumerate() {
        assert_eq!(r.rfind(elt), Some(i));
    }
}

#[test]
fn test_rev_slice_split() {
    let data = [1, 2, 3, 4];

    let r = <&RevSlice<_>>::from(&data[..]);

    for i in 0..r.len() {
        let (a, b) = r.split_at(i);
        assert_eq!(a, &r[..i]);
        assert_eq!(b, &r[i..]);
    }
}

#[test]
fn test_rev_slice_hash() {
    let data = [1, 2, 3, 4];
    let rev = [4, 3, 2, 1];

    let r = <&RevSlice<_>>::from(&data[..]);

    #[allow(deprecated)]
    fn hash<T: ?Sized + Hash>(value: &T) -> u64 {
        use std::hash::SipHasher;
        let mut h = SipHasher::new();
        value.hash(&mut h);
        h.finish()
    }
    for i in 0..r.len() {
        for j in i..r.len() {
            assert_eq!(hash(&r[i..j]), hash(&rev[i..j]));
        }
    }
}
