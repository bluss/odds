
#[macro_use]
extern crate quickcheck;

extern crate odds;

use odds::slice::unalign::UnalignedIter;
use odds::slice::iter::SliceIter;


quickcheck! {
    fn bit_count(v: Vec<u8>, offset: u8) -> bool {
        // use offset for a random alignment of the data
        if v.len() == 0 {
            return true;
        }
        let offset = offset as usize % v.len();
        let data = &v[offset..];

        let mut c = 0;
        let mut iter = UnalignedIter::<u32>::from_slice(data);
        c += (&mut iter).map(|x| x.count_ones()).sum::<u32>();
        c += iter.tail().map(|x| x.count_ones()).sum::<u32>();
        data.iter().map(|b| b.count_ones()).sum::<u32>() == c


    }
}

use odds::slice::SliceFind;

quickcheck! {
    fn find(v: Vec<i8>, offset: u8, pat: i8) -> bool {
        // use offset for a random alignment of the data
        if v.len() == 0 {
            return true;
        }
        let offset = offset as usize % v.len();
        let data = &v[offset..];

        data.find(&pat) == data.iter().position(|x| *x == pat)
    }

    fn rfind(v: Vec<i8>, offset: u8, pat: i8) -> bool {
        // use offset for a random alignment of the data
        if v.len() == 0 {
            return true;
        }
        let offset = offset as usize % v.len();
        let data = &v[..v.len() - offset];

        data.rfind(&pat) == data.iter().rposition(|x| *x == pat)
    }
}

// SliceIter
quickcheck! {
    fn slice_iter_find(v: Vec<i8>, offset: u8, pat: i8) -> bool {
        // use offset for a random alignment of the data
        if v.len() == 0 {
            return true;
        }
        let offset = offset as usize % v.len();
        let data = &v[offset..];

        data.iter().find(|x| **x == pat) ==
            SliceIter::from(data).find(|x| **x == pat)
    }

    fn slice_iter_position(v: Vec<i8>, offset: u8, pat: i8) -> bool {
        // use offset for a random alignment of the data
        if v.len() == 0 {
            return true;
        }
        let offset = offset as usize % v.len();
        let data = &v[offset..];

        data.iter().position(|x| *x == pat) ==
            SliceIter::from(data).position(|x| *x == pat)
    }

    fn slice_iter_rposition(v: Vec<i8>, offset: u8, pat: i8) -> bool {
        // use offset for a random alignment of the data
        if v.len() == 0 {
            return true;
        }
        let offset = offset as usize % v.len();
        let data = &v[offset..];

        data.iter().rposition(|x| *x == pat) ==
            SliceIter::from(data).rposition(|x| *x == pat)
    }

    fn slice_iter_all(v: Vec<i8>) -> bool {
        v.iter().all(|x| *x == 0) == SliceIter::from(&v[..]).all(|x| *x == 0)
    }
    fn slice_iter_any(v: Vec<i8>) -> bool {
        v.iter().any(|x| *x == 0) == SliceIter::from(&v[..]).any(|x| *x == 0)
    }
}
