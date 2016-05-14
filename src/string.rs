//! Extensions to `&str` and `String`
//!
use std::iter;
#[cfg(feature="std")]
use std::ptr;
use std::str;

use IndexRange;

/// Extra methods for `str`
pub trait StrExt {
    #[cfg(feature="std")]
    /// Repeat the string `n` times.
    ///
    /// Requires `feature="std"`
    fn rep(&self, n: usize) -> String;

    #[cfg(feature="std")]
    /// Requires `feature="std"`
    fn append(&self, s: &str) -> String;

    /// All non-empty prefixes
    fn prefixes(&self) -> Prefixes;

    /// All non-empty suffixes
    fn suffixes(&self) -> Suffixes;

    /// Produce all non-empty substrings
    fn substrings(&self) -> Substrings;

    /// Return `true` if `index` is acceptable for slicing the string.
    ///
    /// Acceptable indices are byte offsets from the start of the string
    /// that mark the start of an encoded utf-8 sequence, or an index equal
    /// to `self.len()`.
    ///
    /// Return `false` if the index is out of bounds.
    ///
    /// For example the string `"Abcαβγ"` has length is 9 and the acceptable
    /// indices are *0, 1, 2, 3, 5, 7,* and *9*.
    ///
    /// ```
    /// use odds::string::StrExt;
    /// for &ix in &[0, 1, 2, 3, 5, 7, 9] {
    ///     assert!("Abcαβγ".is_acceptable_index(ix));
    /// }
    /// ```
    fn is_acceptable_index(&self, index: usize) -> bool;
}

/// Extension trait for `str` for string slicing without panicking
pub trait StrSlice {
    /// Return a slice of the string, if it is in bounds /and on character boundaries/,
    /// otherwise return `None`
    fn get_slice<R>(&self, r: R) -> Option<&str> where R: IndexRange;
}

impl StrExt for str {
    #[cfg(feature="std")]
    fn rep(&self, n: usize) -> String {
        let mut s = String::with_capacity(self.len() * n);
        s.extend((0..n).map(|_| self));
        s
    }

    #[cfg(feature="std")]
    fn append(&self, s: &str) -> String {
        String::from(self) + s
    }

    fn prefixes(&self) -> Prefixes {
        Prefixes { s: self, iter: self.char_indices() }
    }

    fn suffixes(&self) -> Suffixes {
        Suffixes { s: self, iter: self.char_indices() }
    }

    fn substrings(&self) -> Substrings {
        Substrings { iter: self.prefixes().flat_map(str::suffixes) }
    }

    fn is_acceptable_index(&self, index: usize) -> bool {
        if index == 0 || index == self.len() {
            true
        } else {
            self.as_bytes().get(index).map_or(false, |byte| {
                // check it's not a continuation byte
                *byte as i8 >= -0x40
            })
        }
    }
}

impl StrSlice for str {
    fn get_slice<R>(&self, r: R) -> Option<&str> where R: IndexRange {
        let start = r.start().unwrap_or(0);
        let end = r.end().unwrap_or(self.len());
        if self.is_acceptable_index(start) && self.is_acceptable_index(end) {
            Some(&self[start..end])
        } else {
            None
        }
    }
}

/// Iterator of all non-empty prefixes
#[derive(Clone)]
pub struct Prefixes<'a> {
    s: &'a str,
    iter: str::CharIndices<'a>,
}

impl<'a> Iterator for Prefixes<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        self.iter.next().map(|(i, ch)| &self.s[..i + ch.len_utf8()])
    }
}

/// Iterator of all non-empty suffixes
#[derive(Clone)]
pub struct Suffixes<'a> {
    s: &'a str,
    iter: str::CharIndices<'a>,
}

impl<'a> Iterator for Suffixes<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        self.iter.next().map(|(i, _)| &self.s[i..])
    }
}

/// Iterator of all non-empty substrings
#[derive(Clone)]
pub struct Substrings<'a> {
    iter: iter::FlatMap<Prefixes<'a>, Suffixes<'a>, fn(&'a str) -> Suffixes<'a>>,
}

impl<'a> Iterator for Substrings<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<&'a str> {
        self.iter.next()
    }
}

#[cfg(feature="std")]
/// Extra methods for `String`
///
/// Requires `feature="std"`
pub trait StringExt {
    /// **Panics** if `index` is out of bounds.
    fn insert_str(&mut self, index: usize, s: &str);
}

#[cfg(feature="std")]
impl StringExt for String {
    /// **Panics** if `index` is out of bounds.
    fn insert_str(&mut self, index: usize, s: &str) {
        assert!(self.is_acceptable_index(index));
        self.reserve(s.len());
        // move the tail, then copy in the string
        unsafe {
            let v = self.as_mut_vec();
            let ptr = v.as_mut_ptr();
            ptr::copy(ptr.offset(index as isize),
                      ptr.offset((index + s.len()) as isize),
                      v.len() - index);
            ptr::copy_nonoverlapping(s.as_ptr(),
                                     ptr.offset(index as isize),
                                     s.len());
            let new_len = v.len() + s.len();
            v.set_len(new_len);
        }
    }
}

#[test]
fn test_acc_index() {
    let s = "Abcαβγ";
    for (ix, _) in s.char_indices() {
        assert!(s.is_acceptable_index(ix));
    }
    assert!(s.is_acceptable_index(s.len()));
    let indices = [0, 1, 2, 3, 5, 7, 9];

    for &ix in &indices {
        assert!(s.is_acceptable_index(ix));
    }

    let t = "";
    assert!(t.is_acceptable_index(0));
}

#[test]
fn test_string_ext() {
    let mut s = String::new();
    let t = "αβγabc";
    s.insert_str(0, t);
    assert_eq!(s, t);
    s.insert_str(2, "x");
    assert_eq!(s, "αxβγabc");
}

#[test]
fn test_slice() {
    let t = "αβγabc";
    assert_eq!(t.get_slice(..), Some(t));
    assert_eq!(t.get_slice(0..t.len()), Some(t));
    assert_eq!(t.get_slice(1..), None);
    assert_eq!(t.get_slice(0..t.len()+1), None);
    assert_eq!(t.get_slice(t.len()+1..), None);
    assert_eq!(t.get_slice(t.len()..), Some(""));
}
