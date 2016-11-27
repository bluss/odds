//! Blocked iterator


use std::mem::size_of;
use std::marker::PhantomData;

use slice::iter::{SliceIter};
use pointer::ptrdistance;

pub unsafe trait Block {
    type Item;
    fn capacity() -> usize;
}
macro_rules! impl_pod {
    (@array $($e:expr),+) => {
        $(
        unsafe impl<T> Block for [T; $e] {
            type Item = T;
            #[inline(always)]
            fn capacity() -> usize { $e }
        }
        )+
    };
    ($($t:ty)+) => {
        $(
        unsafe impl Block for $t { }
        )+
    };
}
impl_pod!{@array 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16}


/// An iterator that yields blocks out of the underlying data's range.
///
/// A block is a fixed size array of `T`, and each iteration yields a
/// reference to the next block.
///
/// See also the tail methods that provide access to the rest of the elements
/// that did not go up evenly into a block.
#[derive(Debug)]
pub struct BlockedIter<'a, B: 'a, T: 'a> {
    ptr: *const T,
    end: *const T,
    ty1: PhantomData<&'a T>,
    ty2: PhantomData<&'a B>,
}

impl<'a, B, T> Copy for BlockedIter<'a, B, T> { }
impl<'a, B, T> Clone for BlockedIter<'a, B, T> {
    fn clone(&self) -> Self { *self }
}

impl<'a, B, T> BlockedIter<'a, B, T>
    where B: Block<Item=T>,
{
    /*
    /// Create an `BlockedIter` from `ptr` and `end`, which must be spaced
    /// an whole number of `T` offsets apart.
    pub unsafe fn from_raw_parts(ptr: *const T, end: *const T) -> Self {
        /*
        let len = end as usize - ptr as usize;
        debug_assert_eq!(len % size_of::<T>(), 0);
        */
        BlockedIter {
            ptr: ptr,
            end: end,
            ty: PhantomData,
        }
    }
    */

    /// Create an `BlockedIter` out of the slice of data, which iterates first
    /// in blocks of `T`, and then leaves a tail of the remaining
    /// elements.
    pub fn from_slice(data: &'a [T]) -> Self {
        assert!(size_of::<T>() != 0);
        unsafe {
            let ptr = data.as_ptr();
            let len = data.len();
            let end = ptr.offset(len as isize);
            BlockedIter {
                ptr: ptr,
                end: end,
                ty1: PhantomData,
                ty2: PhantomData,
            }
        }
    }

    /// Return an iterator of the remaining tail;
    /// this can be called at any time, but in particular when the iterator
    /// has returned None.
    #[inline(always)]
    pub fn tail(&self) -> SliceIter<'a, T> {
        unsafe {
            SliceIter::new(self.ptr, self.end)
        }
    }

    /// Return `true` if the tail is not empty.
    pub fn has_tail(&self) -> bool {
        self.ptr != self.end
    }

    /// Return the next iterator element, without stepping the iterator.
    pub fn peek_next(&self) -> Option<<Self as Iterator>::Item>
    {
        if ptrdistance(self.ptr, self.end) >= B::capacity() {
            unsafe {
                Some(&*(self.ptr as *const B))
            }
        } else {
            None
        }
    }
}

impl<'a, B, T> Iterator for BlockedIter<'a, B, T>
    where B: Block<Item=T>,
{
    type Item = &'a B;
    fn next(&mut self) -> Option<Self::Item> {
        if ptrdistance(self.ptr, self.end) >= B::capacity() {
            unsafe {
                let elt = Some(&*(self.ptr as *const B));
                self.ptr = self.ptr.offset(B::capacity() as isize);
                elt
            }
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = ptrdistance(self.ptr, self.end) / B::capacity();
        (len, Some(len))
    }
}

impl<'a, B, T> ExactSizeIterator for BlockedIter<'a, B, T>
    where B: Block<Item=T>,
{ }

use std::ops::Index;

impl<'a, B, T> Index<usize> for BlockedIter<'a, B, T>
    where B: Block<Item=T>,
{
    type Output = B;
    fn index(&self, i: usize) -> &Self::Output {
        assert!(i < self.len());
        unsafe {
            &*(self.ptr.offset((i * B::capacity()) as isize) as *const B)
        }
    }
}


#[test]
fn test_blocked() {
    let data = [0, 1, 2, 3, 4];
    let mut iter = BlockedIter::<[u32; 2], _>::from_slice(&data);
    assert_eq!(iter.next(), Some(&[0, 1]));
    assert_eq!(iter.next(), Some(&[2, 3]));
    assert_eq!(iter.next(), None);
    assert_eq!(iter.tail().as_slice(), &[4]);

    let mut iter = BlockedIter::<[u32; 8], _>::from_slice(&data);
    assert_eq!(iter.next(), None);
    assert_eq!(iter.tail().as_slice(), &data);
}

#[test]
fn test_blocked_index() {
    let data = [0, 1, 2, 3, 4];
    let iter = BlockedIter::<[u32; 2], _>::from_slice(&data);
    assert_eq!(iter[0], [0, 1]);
    assert_eq!(iter[1], [2, 3]);
}

#[should_panic]
#[test]
fn test_blocked_index_oob() {
    let data = [0, 1, 2, 3, 4];
    let iter = BlockedIter::<[u32; 2], _>::from_slice(&data);
    iter[2];
}
