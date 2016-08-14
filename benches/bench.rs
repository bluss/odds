
#![feature(test)]
extern crate test;

extern crate odds;

use odds::slice::shared_prefix;

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
