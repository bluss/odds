//! Extensions to `Vec`

use range::IndexRange;
use std::ptr;
use std::slice;

/// Extra methods for `Vec<T>`
pub trait VecExt<T> {
    /// Remove elements in a range, and insert from an iterator in their place.
    ///
    /// The removed and inserted ranges don't have to match in length.
    ///
    /// **Panics** if range `r` is out of bounds.
    ///
    /// **Panics** if iterator `iter` is not of exact length.
    fn splice<R, I>(&mut self, r: R, iter: I)
        where I: IntoIterator<Item=T>,
              I::IntoIter: ExactSizeIterator,
              R: IndexRange;
}

/// `Vec::splice`: Remove elements in a range, and insert from an iterator
/// in their place.
///
/// The removed and inserted ranges don't have to match in length.
///
/// **Panics** if range `r` is out of bounds.
///
/// **Panics** if iterator `iter` is not of exact length.
impl<T> VecExt<T> for Vec<T> {
    fn splice<R, I>(&mut self, r: R, iter: I)
        where I: IntoIterator<Item=T>,
              I::IntoIter: ExactSizeIterator,
              R: IndexRange,
    {
        let v = self;
        let mut iter = iter.into_iter();
        let (input_len, _) = iter.size_hint();
        let old_len = v.len();
        let r = r.start().unwrap_or(0)..r.end().unwrap_or(old_len);
        assert!(r.start <= r.end);
        assert!(r.end <= v.len());
        let rm_len = r.end - r.start;
        v.reserve(input_len.saturating_sub(rm_len));

        unsafe {
            let ptr = v.as_mut_ptr();
            v.set_len(r.start);

            // drop all elements in `r`
            {
                let mslc = slice::from_raw_parts_mut(ptr.offset(r.start as isize), rm_len);
                for elt_ptr in mslc {
                    ptr::read(elt_ptr); // Possible panic
                }
            }

            if rm_len != input_len {
                // move tail elements
                ptr::copy(ptr.offset(r.end as isize),
                          ptr.offset((r.start + input_len) as isize),
                          old_len - r.end);
            }

            // fill in elements from the iterator
            // FIXME: On panic, drop tail properly too (using panic guard)
            {
                let grow_slc = slice::from_raw_parts_mut(ptr.offset(r.start as isize), input_len);
                let mut len = r.start;
                for slot_ptr in grow_slc {
                    if let Some(input_elt) = iter.next() { // Possible Panic
                        ptr::write(slot_ptr, input_elt);
                    } else {
                        // FIXME: Skip check with trusted iterators
                        panic!("splice: iterator too short");
                    }
                    // update length to drop as much as possible on panic
                    len += 1;
                    v.set_len(len);
                }
                v.set_len(old_len - rm_len + input_len);
            }
        }
        //assert!(iter.next().is_none(), "splice: iterator not exact size");
    }
}

#[test]
fn test_splice() {

    let mut v = vec![1, 2, 3, 4];
    v.splice(1..1, vec![9, 9]);
    assert_eq!(v, &[1, 9, 9, 2, 3, 4]);

    let mut v = vec![1, 2, 3, 4];
    v.splice(1..2, vec![9, 9]);
    assert_eq!(v, &[1, 9, 9, 3, 4]);

    let mut v = vec![1, 2, 3, 4, 5];
    v.splice(1..4, vec![9, 9]);
    assert_eq!(v, &[1, 9, 9, 5]);

    let mut v = vec![1, 2, 3, 4];
    v.splice(0..4, Some(9));
    assert_eq!(v, &[9]);

    let mut v = vec![1, 2, 3, 4];
    v.splice(0..4, None);
    assert_eq!(v, &[]);

    let mut v = vec![1, 2, 3, 4];
    v.splice(1.., Some(9));
    assert_eq!(v, &[1, 9]);
}
