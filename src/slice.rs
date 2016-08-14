
use std::ptr;
use std::cmp::min;

/// Unaligned load of a u64 at index `i` in `buf`
unsafe fn load_u64(buf: &[u8], i: usize) -> u64 {
    debug_assert!(i + 8 <= buf.len());
    let mut data = 0u64;
    ptr::copy_nonoverlapping(buf.get_unchecked(i), &mut data as *mut _ as *mut u8, 8);
    data
}

/// Return the end index of the longest shared (equal) prefix of `a` and `b`.
pub fn shared_prefix(a: &[u8], b: &[u8]) -> usize {
    let len = min(a.len(), b.len());
    let mut a = &a[..len];
    let mut b = &b[..len];
    let mut offset = 0;
    while a.len() >= 16 {
        unsafe {
            let a0 = load_u64(a, 0);
            let a1 = load_u64(a, 8);
            let b0 = load_u64(b, 0);
            let b1 = load_u64(b, 8);
            let d0 = a0 ^ b0;
            let d1 = a1 ^ b1;
            if d0 ^ d1 != 0 {
            //if d0 != 0 || d1 != 0 {
                break;
            }
        }
        offset += 16;
        a = &a[16..];
        b = &b[16..];
    }
    for i in 0..a.len() {
        if a[i] != b[i] {
            return offset + i;
        }
    }
    len
}


#[test]
fn correct() {
    let mut a = [0xff; 1024];
    let b = [0xff; 1024];
    for byte in 0..255 { // don't test byte 255
        for i in 0..a.len() {
            a[i] = byte;
            let ans = shared_prefix(&a, &b);
            assert!(ans == i, "failed for index {} and byte {:x} (got ans={})",
                    i, byte, ans);
            a[i] = 0xff;
        }
    }
}
