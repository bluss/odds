//! Extensions to `Vec`
//!
//! Requires `feature="std"`
#![cfg(feature="std")]

use slice::SliceFind;


/// Create a new vec from the iterable
pub fn vec<I>(iterable: I) -> Vec<I::Item>
    where I: IntoIterator
{
    iterable.into_iter().collect()
}


/// Extra methods for `Vec<T>`
///
/// Requires `feature="std"`
pub trait VecExt<T> {
    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` such that `f(&mut e)` returns false.
    /// This method operates in place and preserves the order of the retained
    /// elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use odds::vec::VecExt;
    /// let mut vec = vec![1, 2, 3, 4];
    /// vec.retain_mut(|x| {
    ///     let keep = *x % 2 == 0;
    ///     *x *= 10;
    ///     keep
    /// });
    /// assert_eq!(vec, [20, 40]);
    /// ```
    fn retain_mut<F>(&mut self, f: F)
        where F: FnMut(&mut T) -> bool;
}

impl<T> VecExt<T> for Vec<T> {
    // Adapted from libcollections/vec.rs in Rust
    // Primary author in Rust: Michael Darakananda
    fn retain_mut<F>(&mut self, mut f: F)
        where F: FnMut(&mut T) -> bool
    {
        let len = self.len();
        let mut del = 0;
        {
            let v = &mut **self;

            for i in 0..len {
                if !f(&mut v[i]) {
                    del += 1;
                } else if del > 0 {
                    v.swap(i - del, i);
                }
            }
        }
        if del > 0 {
            self.truncate(len - del);
        }
    }
}




pub trait VecFindRemove {
    type Item;
    /// Linear search for the first element equal to `elt` and remove
    /// it if found.
    ///
    /// Return its index and the value itself.
    fn find_remove<U>(&mut self, elt: &U) -> Option<(usize, Self::Item)>
        where Self::Item: PartialEq<U>;

    /// Linear search for the last element equal to `elt` and remove
    /// it if found.
    ///
    /// Return its index and the value itself.
    fn rfind_remove<U>(&mut self, elt: &U) -> Option<(usize, Self::Item)>
        where Self::Item: PartialEq<U>;
}

impl<T> VecFindRemove for Vec<T> {
    type Item = T;
    fn find_remove<U>(&mut self, elt: &U) -> Option<(usize, Self::Item)>
        where Self::Item: PartialEq<U>
    {
        self.find(elt).map(|i| (i, self.remove(i)))
    }
    fn rfind_remove<U>(&mut self, elt: &U) -> Option<(usize, Self::Item)>
        where Self::Item: PartialEq<U>
    {
        self.rfind(elt).map(|i| (i, self.remove(i)))
    }
}

#[test]
fn test_find() {
    let mut v = vec![0, 1, 2, 3, 1, 2, 1];
    assert_eq!(v.rfind_remove(&1), Some((6, 1)));
    assert_eq!(v.find_remove(&2), Some((2, 2)));
    assert_eq!(v.find_remove(&7), None);
    assert_eq!(&v, &[0, 1, 3, 1, 2]);
}
