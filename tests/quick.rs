
#[macro_use]
extern crate quickcheck;

extern crate odds;

use odds::slice::unalign::UnalignedIter;


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

