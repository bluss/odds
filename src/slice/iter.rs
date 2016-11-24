//! Slice iterators

use std::mem::size_of;
use std::marker::PhantomData;
use std::ops::Index;

/// Slice (contiguous data) iterator.
///
/// Iterator element type is `T` (by value).
/// This iterator exists mainly to have the constructor from a pair
/// of raw pointers available, which the libcore slice iterator does not allow.
///
/// Implementation note: Aliasing/optimization issues disappear if we use
/// non-pointer iterator element type, so we use `T`. (The libcore slice
/// iterator has `assume` and other tools available to combat it).
///
/// `T` must not be a zero sized type.
#[derive(Debug)]
pub struct SliceCopyIter<'a, T: 'a> {
    ptr: *const T,
    end: *const T,
    ty: PhantomData<&'a T>,
}

impl<'a, T> Copy for SliceCopyIter<'a, T> { }
impl<'a, T> Clone for SliceCopyIter<'a, T> {
    fn clone(&self) -> Self { *self }
}

impl<'a, T> SliceCopyIter<'a, T>
    where T: Copy
{
    #[inline]
    pub unsafe fn new(ptr: *const T, end: *const T) -> Self {
        assert!(size_of::<T>() != 0);
        SliceCopyIter {
            ptr: ptr,
            end: end,
            ty: PhantomData,
        }
    }

    /// Return the start, end pointer of the iterator
    pub fn into_raw(self) -> (*const T, *const T) {
        (self.ptr, self.end)
    }

    /// Return the start pointer
    pub fn start(&self) -> *const T {
        self.ptr
    }

    /// Return the end pointer
    pub fn end(&self) -> *const T {
        self.end
    }
}

impl<'a, T> Iterator for SliceCopyIter<'a, T>
    where T: Copy,
{
    type Item = T;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.ptr != self.end {
            unsafe {
                let elt = Some(*self.ptr);
                self.ptr = self.ptr.offset(1);
                elt
            }
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = (self.end as usize - self.ptr as usize) / size_of::<T>();
        (len, Some(len))
    }

    fn count(self) -> usize {
        self.len()
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, T> DoubleEndedIterator for SliceCopyIter<'a, T>
    where T: Copy
{
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.ptr != self.end {
            unsafe {
                self.end = self.end.offset(-1);
                let elt = Some(*self.end);
                elt
            }
        } else {
            None
        }
    }
}

impl<'a, T> ExactSizeIterator for SliceCopyIter<'a, T> where T: Copy { }

impl<'a, T> From<&'a [T]> for SliceCopyIter<'a, T>
    where T: Copy
{
    fn from(slice: &'a [T]) -> Self {
        assert!(size_of::<T>() != 0);
        unsafe {
            let ptr = slice.as_ptr();
            let end = ptr.offset(slice.len() as isize);
            SliceCopyIter::new(ptr, end)
        }
    }
}

impl<'a, T> Default for SliceCopyIter<'a, T>
    where T: Copy
{
    /// Create an empty `SliceCopyIter`.
    fn default() -> Self {
        unsafe {
            SliceCopyIter::new(0x1 as *const T, 0x1 as *const T)
        }
    }
}

impl<'a, T> Index<usize> for SliceCopyIter<'a, T>
    where T: Copy
{
    type Output = T;
    fn index(&self, i: usize) -> &T {
        assert!(i < self.len());
        unsafe {
            &*self.ptr.offset(i as isize)
        }
    }
}

/// Slice (contiguous data) iterator.
///
/// Iterator element type is `&T`
/// This iterator exists mainly to have the constructor from a pair
/// of raw pointers available, which the libcore slice iterator does not allow.
///
/// `T` must not be a zero sized type.
#[derive(Debug)]
pub struct SliceIter<'a, T: 'a> {
    ptr: *const T,
    end: *const T,
    ty: PhantomData<&'a T>,
}

impl<'a, T> Copy for SliceIter<'a, T> { }
impl<'a, T> Clone for SliceIter<'a, T> {
    fn clone(&self) -> Self { *self }
}

impl<'a, T> SliceIter<'a, T> {
    /// Create a new slice iterator
    ///
    /// See also ``SliceIter::from, SliceIter::default``.
    #[inline]
    pub unsafe fn new(ptr: *const T, end: *const T) -> Self {
        assert!(size_of::<T>() != 0);
        SliceIter {
            ptr: ptr,
            end: end,
            ty: PhantomData,
        }
    }

    /// Return the start pointer
    pub fn start(&self) -> *const T {
        self.ptr
    }

    /// Return the end pointer
    pub fn end(&self) -> *const T {
        self.end
    }

    /// Return the next iterator element, without stepping the iterator.
    pub fn peek_next(&self) -> Option<<Self as Iterator>::Item>
    {
        if self.ptr != self.end {
            unsafe {
                Some(&*self.ptr)
            }
        } else {
            None
        }
    }
}

impl<'a, T> Iterator for SliceIter<'a, T> {
    type Item = &'a T;
    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.ptr != self.end {
            unsafe {
                Some(&*self.ptr.post_inc())
            }
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = (self.end as usize - self.ptr as usize) / size_of::<T>();
        (len, Some(len))
    }

    fn count(self) -> usize {
        self.len()
    }

    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }

    fn all<F>(&mut self, mut predicate: F) -> bool
        where F: FnMut(Self::Item) -> bool,
    {
        self.fold_while(true, move |_, elt| {
            if predicate(elt) {
                FoldWhile::Continue(true)
            } else {
                FoldWhile::Done(false)
            }
        })
    }

    fn any<F>(&mut self, mut predicate: F) -> bool
        where F: FnMut(Self::Item) -> bool,
    {
        !self.all(move |x| !predicate(x))
    }

    fn find<F>(&mut self, mut predicate: F) -> Option<Self::Item>
        where F: FnMut(&Self::Item) -> bool,
    {
        self.fold_while(None, move |_, elt| {
            if predicate(&elt) {
                FoldWhile::Done(Some(elt))
            } else {
                FoldWhile::Continue(None)
            }
        })
    }

    fn position<F>(&mut self, mut predicate: F) -> Option<usize>
        where F: FnMut(Self::Item) -> bool,
    {
        let start = self.ptr;
        self.fold_while(None, move |_, elt| {
            if predicate(elt) {
                FoldWhile::Done(Some(ptrdistance(start, elt)))
            } else {
                FoldWhile::Continue(None)
            }
        })
    }
}

#[inline(always)]
fn ptrdistance<T>(a: *const T, b: *const T) -> usize {
    (b as usize - a as usize) / size_of::<T>()
}

impl<'a, T> DoubleEndedIterator for SliceIter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.ptr != self.end {
            unsafe {
                Some(&*self.end.pre_dec())
            }
        } else {
            None
        }
    }
}

impl<'a, T> ExactSizeIterator for SliceIter<'a, T> { }

impl<'a, T> From<&'a [T]> for SliceIter<'a, T> {
    fn from(slice: &'a [T]) -> Self {
        assert!(size_of::<T>() != 0);
        unsafe {
            let ptr = slice.as_ptr();
            let end = ptr.offset(slice.len() as isize);
            SliceIter::new(ptr, end)
        }
    }
}

impl<'a, T> Default for SliceIter<'a, T> {
    /// Create an empty `SliceIter`.
    fn default() -> Self {
        unsafe {
            SliceIter::new(0x1 as *const T, 0x1 as *const T)
        }
    }
}

impl<'a, T> Index<usize> for SliceIter<'a, T> {
    type Output = T;
    fn index(&self, i: usize) -> &T {
        assert!(i < self.len());
        unsafe {
            &*self.ptr.offset(i as isize)
        }
    }
}



/// Extension methods for raw pointers
pub trait PointerExt : Copy {
    unsafe fn offset(self, i: isize) -> Self;

    /// Increment by 1
    #[inline(always)]
    unsafe fn inc(&mut self) {
        *self = self.offset(1);
    }

    /// Increment the pointer by 1, but return its old value.
    #[inline(always)]
    unsafe fn post_inc(&mut self) -> Self {
        let current = *self;
        *self = self.offset(1);
        current
    }

    /// Increment the pointer by 1, but return its old value.
    #[inline(always)]
    unsafe fn pre_dec(&mut self) -> Self {
        *self = self.offset(-1);
        *self
    }

    /// Decrement by 1
    #[inline(always)]
    unsafe fn dec(&mut self) {
        *self = self.offset(-1);
    }

    /// Offset by `s` multiplied by `index`.
    #[inline(always)]
    unsafe fn stride_offset(self, s: isize, index: usize) -> Self {
        self.offset(s * index as isize)
    }
}

impl<T> PointerExt for *const T {
    #[inline(always)]
    unsafe fn offset(self, i: isize) -> Self {
        self.offset(i)
    }
}

impl<T> PointerExt for *mut T {
    #[inline(always)]
    unsafe fn offset(self, i: isize) -> Self {
        self.offset(i)
    }
}


#[derive(Copy, Clone, Debug)]
/// An enum used for controlling the execution of `.fold_while()`.
pub enum FoldWhile<T> {
    /// Continue folding with this value
    Continue(T),
    /// Fold is complete and will return this value
    Done(T),
}

impl<T> FoldWhile<T> {
    /// Return the inner value.
    pub fn into_inner(self) -> T {
        match self {
            FoldWhile::Continue(t) => t,
            FoldWhile::Done(t) => t,
        }
    }
}

trait FoldWhileExt : Iterator {
    // Note: For composability (if used with adaptors, return type
    // should be FoldWhile<Acc> then instead.)
    fn fold_while<Acc, G>(&mut self, init: Acc, g: G) -> Acc
        where Self: Sized,
              G: FnMut(Acc, Self::Item) -> FoldWhile<Acc>;
}

macro_rules! fold_while {
    ($e:expr) => {
        match $e {
            FoldWhile::Continue(t) => t,
            FoldWhile::Done(done) => return done,
        }
    }
}

impl<'a, T> FoldWhileExt for SliceIter<'a, T> {
    fn fold_while<Acc, G>(&mut self, init: Acc, mut g: G) -> Acc
        where Self: Sized,
              G: FnMut(Acc, Self::Item) -> FoldWhile<Acc>
    {

        let mut accum = init;
        unsafe {
            while ptrdistance(self.ptr, self.end) >= 4 {
                accum = fold_while!(g(accum, &*self.ptr.post_inc()));
                accum = fold_while!(g(accum, &*self.ptr.post_inc()));
                accum = fold_while!(g(accum, &*self.ptr.post_inc()));
                accum = fold_while!(g(accum, &*self.ptr.post_inc()));
            }
            let dist = ptrdistance(self.ptr, self.end);
            if dist >= 3 {
                accum = fold_while!(g(accum, &*self.ptr.post_inc()));
            }
            if dist >= 2 {
                accum = fold_while!(g(accum, &*self.ptr.post_inc()));
            }
            if dist >= 1 {
                accum = fold_while!(g(accum, &*self.ptr.post_inc()));
            }
        }
        accum
    }
}
