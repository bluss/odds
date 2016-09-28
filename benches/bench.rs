
#![feature(test)]
extern crate test;

extern crate odds;
extern crate memchr;
extern crate itertools;

use odds::slice::shared_prefix;
use itertools::enumerate;

use test::Bencher;

#[bench]
fn shpfx(bench: &mut Bencher) {
    let a = vec![0; 64 * 1024 * 1024];
    let mut b = vec![0; 64 * 1024 * 1024];
    const OFF: usize = 47 * 1024 * 1024;
    b[OFF] = 1;

    bench.iter(|| {
        shared_prefix(&a, &b);
    });
    bench.bytes = OFF as u64;
}

#[bench]
fn shpfx_short(bench: &mut Bencher) {
    let a = vec![0; 64 * 1024];
    let mut b = vec![0; 64 * 1024];
    const OFF: usize = 47 * 1024;
    b[OFF] = 1;

    bench.iter(|| {
        shared_prefix(&a, &b);
    });
    bench.bytes = OFF as u64;
}

fn bench_data() -> Vec<u8> { vec![b'z'; 10_000] }

#[bench]
fn optimized_memchr(b: &mut test::Bencher) {
    let haystack = bench_data();
    let needle = b'a';
    b.iter(|| {
        memchr::memchr(needle, &haystack)
    });
    b.bytes = haystack.len() as u64;
}

#[bench]
fn odds_memchr(b: &mut Bencher) {
    let haystack = bench_data();
    let needle = b'a';
    b.iter(|| {
        memchr_mockup(needle, &haystack[1..])
    });
    b.bytes = haystack.len() as u64;
}

// use truncation
const LO_USIZE: usize = 0x0101010101010101 as usize;
const HI_USIZE: usize = 0x8080808080808080 as usize;

/// Return `true` if `x` contains any zero byte.
///
/// From *Matters Computational*, J. Arndt
///
/// "The idea is to subtract one from each of the bytes and then look for
/// bytes where the borrow propagated all the way to the most significant
/// bit."
#[inline]
fn contains_zero_byte(x: usize) -> bool {
    x.wrapping_sub(LO_USIZE) & !x & HI_USIZE != 0
}

fn find<T>(pat: T, text: &[T]) -> Option<usize>
    where T: PartialEq
{
    text.iter().position(|x| *x == pat)
}

fn find_shorter_than<Shorter>(pat: u8, text: &[u8]) -> Option<usize> {
    use std::mem::size_of;
    use std::cmp::min;
    let len = min(text.len(), size_of::<Shorter>() - 1);
    let text = &text[..len];
    for i in 0..len {
        if text[i] == pat {
            return Some(i);
        }
    }
    None
}

// quick and dumb memchr copy
fn memchr_mockup(pat: u8, text: &[u8]) -> Option<usize> {
    use std::mem::size_of;
    type T = [usize; 2];
    let block_size = size_of::<T>();
    let (a, b, c) = odds::slice::split_aligned_for::<T>(text);
    if let r @ Some(_) = find_shorter_than::<T>(pat, a) {
        return r;
    }

    let rep = LO_USIZE * (pat as usize);
    let mut reach = None;
    for (i, block) in enumerate(b) {
        let f1 = contains_zero_byte(rep ^ block[0]);
        let f2 = contains_zero_byte(rep ^ block[1]);
        if f1 || f2 {
            reach = Some(i);
            break;
        }
    }
    if let Some(i) = reach {
        find(pat, &text[i * block_size..]).map(|pos| pos + a.len())
    } else {
        find_shorter_than::<T>(pat, c).map(|pos| pos + text.len() - c.len())
    }
}
