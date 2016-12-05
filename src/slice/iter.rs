//! Slice iterators

use std::mem::size_of;
use std::marker::PhantomData;
use std::ops::Index;
use std::slice;

use pointer::ptrdistance;

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

    pub fn as_slice(&self) -> &'a [T] {
        unsafe {
            slice::from_raw_parts(self.ptr, self.len())
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
        let len = self.len();
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
        self.fold_ok(true, move |_, elt| {
            if predicate(elt) {
                Ok(true)
            } else {
                Err(false)
            }
        }).unwrap_or_else(|e| e)
    }

    fn any<F>(&mut self, mut predicate: F) -> bool
        where F: FnMut(Self::Item) -> bool,
    {
        !self.all(move |x| !predicate(x))
    }

    fn find<F>(&mut self, mut predicate: F) -> Option<Self::Item>
        where F: FnMut(&Self::Item) -> bool,
    {
        self.fold_ok((), move |_, elt| {
            if predicate(&elt) {
                Err(elt)
            } else {
                Ok(())
            }
        }).err()
    }

    fn position<F>(&mut self, mut predicate: F) -> Option<usize>
        where F: FnMut(Self::Item) -> bool,
    {
        let mut index = 0;
        self.fold_ok((), move |_, elt| {
            if predicate(elt) {
                Err(index)
            } else {
                index += 1;
                Ok(())
            }
        }).err()
    }

    fn rposition<F>(&mut self, mut predicate: F) -> Option<usize>
        where F: FnMut(Self::Item) -> bool,
    {
        let mut index = self.len();
        self.rfold_ok((), move |_, elt| {
            index -= 1;
            if predicate(elt) {
                Err(index)
            } else {
                Ok(())
            }
        }).err()
    }
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

impl<'a, T> ExactSizeIterator for SliceIter<'a, T> {
    fn len(&self) -> usize {
        ptrdistance(self.ptr, self.end)
    }
}

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

struct MockTake<I> {
    n: usize,
    iter: I,
}

impl<I> Iterator for MockTake<I> where I: Iterator {
    type Item = I::Item;
    fn next(&mut self) -> Option<Self::Item> {
        if self.n > 0 {
            self.n -= 1;
            self.iter.next()
        } else {
            None
        }
    }
}

enum TakeStop<L, R> {
    Their(L),
    Our(R),
}

impl<I> FoldWhileExt for MockTake<I>
    where I: Iterator + FoldWhileExt,
{
    fn fold_ok<Acc, E, G>(&mut self, init: Acc, mut g: G) -> Result<Acc, E>
        where G: FnMut(Acc, Self::Item) -> Result<Acc, E>
    {
        if self.n == 0 {
            Ok(init)
        } else {
            let n = &mut self.n;
            let result = self.iter.fold_ok(init, move |acc, elt| {
                *n -= 1;
                let res = try!(match g(acc, elt) {
                    Err(e) => Err(TakeStop::Their(e)),
                    Ok(x) => Ok(x),
                });
                if *n == 0 {
                    Err(TakeStop::Our(res))
                } else {
                    Ok(res)
                }
            });
            match result {
                Err(TakeStop::Their(e)) => Err(e),
                Err(TakeStop::Our(x)) => Ok(x),
                Ok(x) => Ok(x)
            }
        }
    }
}

#[test]
fn test_mock_take() {
    let data = [1, 2, 3];
    let mut iter = MockTake { n: 2, iter: SliceIter::from(&data[..]) };
    assert_eq!(iter.fold_ok(0, |acc, &elt| Ok::<_, ()>(acc + elt)), Ok(3));
    assert_eq!(iter.next(), None);
    let mut iter = MockTake { n: 2, iter: SliceIter::from(&data[..]) };
    assert_eq!(iter.fold_ok(0, |_, &elt| Err(elt)), Err(1));
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

pub trait FoldWhileExt : Iterator {
    // Note: For composability (if used with adaptors, return type
    // should be FoldWhile<Acc> then instead.)
    /// Starting with initial accumulator `init`, combine the accumulator
    /// with each iterator element using the closure `g` until it returns
    /// `Err` or the iterator’s end is reached.
    /// The last `Result` value is returned.
    fn fold_ok<Acc, E, G>(&mut self, init: Acc, mut g: G) -> Result<Acc, E>
        where Self: Sized,
              G: FnMut(Acc, Self::Item) -> Result<Acc, E>
    {
        let mut accum = init;
        while let Some(elt) = self.next() {
            accum = g(accum, elt)?;
        }
        Ok(accum)
    }

    /// Starting with initial accumulator `init`, combine the accumulator
    /// with each iterator element from the back using the closure `g` until it
    /// returns `Err` or the iterator’s end is reached.
    /// The last `Result` value is returned.
    fn rfold_ok<Acc, E, G>(&mut self, init: Acc, mut g: G) -> Result<Acc, E>
        where Self: Sized + DoubleEndedIterator,
              G: FnMut(Acc, Self::Item) -> Result<Acc, E>
    {
        let mut accum = init;
        while let Some(elt) = self.next_back() {
            accum = g(accum, elt)?;
        }
        Ok(accum)
    }
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
    fn fold_ok<Acc, E, G>(&mut self, init: Acc, mut g: G) -> Result<Acc, E>
        where G: FnMut(Acc, Self::Item) -> Result<Acc, E>
    {

        let mut accum = init;
        unsafe {
            while ptrdistance(self.ptr, self.end) >= 4 {
                accum = try!(g(accum, &*self.ptr.post_inc()));
                accum = try!(g(accum, &*self.ptr.post_inc()));
                accum = try!(g(accum, &*self.ptr.post_inc()));
                accum = try!(g(accum, &*self.ptr.post_inc()));
            }
            while self.ptr != self.end {
                accum = try!(g(accum, &*self.ptr.post_inc()));
            }
        }
        Ok(accum)
    }

    fn rfold_ok<Acc, E, G>(&mut self, mut accum: Acc, mut g: G) -> Result<Acc, E>
        where G: FnMut(Acc, Self::Item) -> Result<Acc, E>
    {
        // manual unrolling is needed when there are conditional exits from the loop's body.
        unsafe {
            while ptrdistance(self.ptr, self.end) >= 4 {
                accum = try!(g(accum, &*self.end.pre_dec()));
                accum = try!(g(accum, &*self.end.pre_dec()));
                accum = try!(g(accum, &*self.end.pre_dec()));
                accum = try!(g(accum, &*self.end.pre_dec()));
            }
            while self.ptr != self.end {
                accum = try!(g(accum, &*self.end.pre_dec()));
            }
        }
        Ok(accum)
    }
}
