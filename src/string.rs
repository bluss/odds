//! Extensions to `&str` and `String`
//!
use std::iter;
use std::ptr;
use std::str;

/// Extra methods for `str`
pub trait StrExt {
    /// Repeat the string `n` times.
    fn rep(&self, n: usize) -> String;

    fn append(&self, s: &str) -> String;

    /// All non-empty prefixes
    fn prefixes(&self) -> Prefixes;

    /// All non-empty suffixes
    fn suffixes(&self) -> Suffixes;

    /// Produce all non-empty substrings
    fn substrings(&self) -> Substrings;
}

impl StrExt for str {
    fn rep(&self, n: usize) -> String {
        let mut s = String::with_capacity(self.len() * n);
        s.extend((0..n).map(|_| self));
        s
    }

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

/// Mask of the value bits of a continuation byte
const CONT_MASK: u8 = 0b0011_1111;
/// Value of the tag bits (tag mask is !CONT_MASK) of a continuation byte
const TAG_CONT_U8: u8 = 0b1000_0000;

fn is_acceptable_str_index(s: &str, index: usize) -> bool {
    if index == s.len() {
        true
    } else {
        s.as_bytes().get(index).map_or(false, |byte| {
            // check it's not a continuation byte
            (byte & !CONT_MASK) != TAG_CONT_U8
        })
    }
}

/// Extra methods for `String`
pub trait StringExt {
    /// **Panics** if `index` is out of bounds.
    fn insert_str(&mut self, index: usize, s: &str);
}

impl StringExt for String {
    /// **Panics** if `index` is out of bounds.
    fn insert_str(&mut self, index: usize, s: &str) {
        assert!(is_acceptable_str_index(self, index));
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
    let s = "αβγabc";
    for (ix, _) in s.char_indices() {
        assert!(is_acceptable_str_index(s, ix));
    }
    assert!(is_acceptable_str_index(s, s.len()));
    let t = "";
    assert!(is_acceptable_str_index(t, 0));
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
