//! Extensions to `&str` and `String`
//!
use crate::std::iter;
#[cfg(feature="std-string")]
use std::ptr;
use crate::std::str;
use crate::std::ops::Deref;

use crate::IndexRange;

/// Extra methods for `str`
pub trait StrExt {
    #[cfg(feature="std-string")]
    /// Repeat the string `n` times.
    ///
    /// Requires `feature="std"`
    #[deprecated(note="Use str::repeat instead")]
    fn rep(&self, n: usize) -> String;

    #[cfg(feature="std-string")]
    /// Requires `feature="std"`
    fn append(&self, s: &str) -> String;

    /// All non-empty prefixes
    fn prefixes(&self) -> Prefixes;

    /// All non-empty suffixes
    fn suffixes(&self) -> Suffixes;

    /// Produce all non-empty substrings
    fn substrings(&self) -> Substrings;
}

/// Extension trait for `str` for string slicing without panicking
#[deprecated(note="Use str::get with a range instead")]
pub trait StrSlice {
    /// Return a slice of the string, if it is in bounds /and on character boundaries/,
    /// otherwise return `None`
    #[deprecated(note="Use str::get with a range instead")]
    fn get_slice<R>(&self, r: R) -> Option<&str> where R: IndexRange;
}

impl StrExt for str {
    #[cfg(feature="std-string")]
    fn rep(&self, n: usize) -> String {
        let mut s = String::with_capacity(self.len() * n);
        s.extend((0..n).map(|_| self));
        s
    }

    #[cfg(feature="std-string")]
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
}

#[allow(deprecated)]
impl StrSlice for str {
    fn get_slice<R>(&self, r: R) -> Option<&str> where R: IndexRange {
        let start = r.start().unwrap_or(0);
        let end = r.end().unwrap_or(self.len());
        if start <= end && self.is_char_boundary(start) && self.is_char_boundary(end) {
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

#[cfg(feature = "std-string")]
/// Extra methods for `String`
///
/// Requires `feature="std-string"`
pub trait StringExt {
    /// **Panics** if `index` is out of bounds.
    #[deprecated(note="Use String::insert_str")]
    fn insert_str(&mut self, index: usize, s: &str);
}

#[cfg(feature="std-string")]
impl StringExt for String {
    /// **Panics** if `index` is out of bounds.
    fn insert_str(&mut self, index: usize, s: &str) {
        assert!(self.is_char_boundary(index));
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

/// Extension traits for the `char_chunks` and `char_windows` methods
pub trait StrChunksWindows {
    /// Return an iterator that splits the string in substrings of each `n`
    /// `char` per substring. The last item will contain the remainder if
    /// `n` does not divide the char length of the string evenly.
    fn char_chunks(&self, n: usize) -> CharChunks;

    /// Return an iterator that produces substrings of each `n`
    /// `char` per substring in a sliding window that advances one char at a time.
    ///
    /// ***Panics*** if `n` is zero.
    fn char_windows(&self, n: usize) -> CharWindows;
}

impl StrChunksWindows for str {
    fn char_chunks(&self, n: usize) -> CharChunks {
        CharChunks::new(self, n)
    }

    fn char_windows(&self, n: usize) -> CharWindows {
        CharWindows::new(self, n)
    }
}

/// An iterator that splits the string in substrings of each `n`
/// `char` per substring. The last item will contain the remainder if
/// `n` does not divide the char length of the string evenly.
#[derive(Clone, Debug)]
pub struct CharChunks<'a> {
    s: &'a str,
    n: usize,
}

impl<'a> CharChunks<'a> {
    fn new(s: &'a str, n: usize) -> Self {
        CharChunks { s: s, n: n }
    }
}

impl<'a> Iterator for CharChunks<'a> {
    type Item = &'a str;
    fn next(&mut self) -> Option<&'a str> {
        let s = self.s;
        if s.is_empty() {
            return None;
        }
        for (i, (j, ch)) in s.char_indices().enumerate() {
            if i + 1 == self.n {
                // FIXME: Use .split_at() when rust version allows
                let mid = j + ch.len_utf8();
                let (part, tail) = (&s[..mid], &s[mid..]);
                self.s = tail;
                return Some(part);
            }
        }
        self.s = "";
        Some(s)
    }
}

/// An iterator that produces substrings of each `n`
/// `char` per substring in a sliding window that advances one char at a time.
#[derive(Clone, Debug)]
pub struct CharWindows<'a> {
    s: &'a str,
    a: usize,
    b: usize,
}

impl<'a> CharWindows<'a> {
    fn new(s: &'a str, n: usize) -> Self {
        assert!(n != 0);
        match s.char_indices().nth(n - 1) {
            None => CharWindows { s: s, a: s.len(), b: s.len() },
            Some((i, ch)) => CharWindows { s: s, a: 0, b: i + ch.len_utf8() }
        }
    }
}

fn char_get(s: &str, i: usize) -> Option<char> {
    s[i..].chars().next()
}

impl<'a> Iterator for CharWindows<'a> {
    type Item = &'a str;
    fn next(&mut self) -> Option<&'a str> {
        let elt;
        // `a` is out of bounds when we are done
        if let Some(c) = char_get(self.s, self.a) {
            elt = &self.s[self.a..self.b];
            self.a += c.len_utf8();
        } else {
            return None;
        }
        if let Some(c) = char_get(self.s, self.b) {
            self.b += c.len_utf8();
        } else {
            self.a = self.s.len();
        }
        Some(elt)
    }
}

/// A single-char string.
#[derive(Copy, Clone, Debug)]
pub struct CharStr {
    buf: [u8; 4],
    len: u32,
}

impl CharStr {
    /// Create a new string from `c`.
    pub fn new(c: char) -> CharStr {
        let mut self_ = CharStr {
            buf: [0; 4],
            len: c.len_utf8() as u32,
        };
        let _ = crate::char::encode_utf8(c, &mut self_.buf);
        self_
    }
}

impl Deref for CharStr {
    type Target = str;
    fn deref(&self) -> &str {
        unsafe {
            str::from_utf8_unchecked(&self.buf[..self.len as usize])
        }
    }
}

#[test]
fn test_char_str() {
    let s = CharStr::new('α');
    assert_eq!(&s[..], "α");
}

#[test]
fn str_windows() {
    assert_eq!(CharWindows::new("abc", 4).next(), None);
    assert_eq!(CharWindows::new("abc", 3).next(), Some("abc"));
    assert_eq!(CharWindows::new("abc", 3).count(), 1);
    assert_eq!(CharWindows::new("αbγ", 2).nth(0), Some("αb"));
    assert_eq!(CharWindows::new("αbγ", 2).nth(1), Some("bγ"));
}

#[test]
#[should_panic]
fn str_windows_not_0() {
    CharWindows::new("abc", 0);
}

#[cfg(feature = "std-string")]
#[test]
fn test_string_ext() {
    let mut s = String::new();
    let t = "αβγabc";
    StringExt::insert_str(&mut s, 0, t);
    assert_eq!(s, t);
    StringExt::insert_str(&mut s, 2, "x");
    assert_eq!(s, "αxβγabc");
}

#[allow(deprecated)]
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
