
extern crate itertools;
extern crate odds;

use itertools::Itertools;

/// Like CharIndices iterator, except it yields slices instead
#[derive(Copy, Clone, Debug)]
struct CharSlices<'a> {
    slice: &'a str,
    offset: usize,
}

impl<'a> CharSlices<'a>
{
    pub fn new(s: &'a str) -> Self
    {
        CharSlices {
            slice: s,
            offset: 0,
        }
    }
}

impl<'a> Iterator for CharSlices<'a>
{
    type Item = (usize, &'a str);

    fn next(&mut self) -> Option<Self::Item>
    {
        if self.slice.len() == 0 {
            return None
        }
        // count continuation bytes
        let mut char_len = 1;
        let mut bytes = self.slice.bytes();
        bytes.next();
        for byte in bytes {
            if (byte & 0xC0) != 0x80 {
                break
            }
            char_len += 1;
        }
        let ch_slice;
        unsafe {
            ch_slice = self.slice.slice_unchecked(0, char_len);
            self.slice = self.slice.slice_unchecked(char_len, self.slice.len());
        }
        let off = self.offset;
        self.offset += char_len;
        Some((off, ch_slice))
    }
}

