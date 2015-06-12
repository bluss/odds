
/// Fixpoint combinator for rust closures, generalized over the return type.
///
/// In **Fix\<T, R\>**, **T** is the argument type, and **R** is the return type,
/// **R** defaults to **T**.
///
/// **Fix** only supports function call notation with the nightly channel and
/// the cargo feature ‘unstable’ enabled.
///
/// ```
/// use odds::Fix;
///
/// let c = |f: Fix<i32>, x| if x == 0 { 1 } else { x * f.call(x - 1) };
/// let fact = Fix(&c);
/// assert_eq!(fact.call(5), 120);
///
/// let data = &[true, false];
/// let all_true = |f: Fix<_, _>, x| {
///     let x: &[_] = x;
///     x.len() == 0 || x[0] && f.call(&x[1..])
/// };
/// let all = Fix(&all_true);
/// assert_eq!(all.call(data), false);
///
/// ```
#[cfg_attr(feature="unstable", doc="
```
// using feature `unstable`
use odds::Fix;

let c = |f: Fix<i32>, x| if x == 0 { 1 } else { x * f(x - 1) };
let fact = Fix(&c);
assert_eq!(fact(5), 120);
```
"
)]
pub struct Fix<'a, T, R = T>(pub &'a Fn(Fix<T, R>, T) -> R);

impl<'a, T, R> Fix<'a, T, R> {
    pub fn call(&self, arg: T) -> R {
        let f = *self;
        f.0(f, arg)
    }
}

impl<'a, T, R> Clone for Fix<'a, T, R> {
    fn clone(&self) -> Self { *self }
}

impl<'a, T, R> Copy for Fix<'a, T, R> { }

#[cfg(feature="unstable")]
impl<'a, T, R> FnOnce<(T,)> for Fix<'a, T, R> {
    type Output = R;
    #[inline]
    extern "rust-call" fn call_once(self, x: (T,)) -> R {
        self.call(x.0)
    }
}

#[cfg(feature="unstable")]
impl<'a, T, R> FnMut<(T,)> for Fix<'a, T, R> {
    #[inline]
    extern "rust-call" fn call_mut(&mut self, x: (T,)) -> R {
        self.call(x.0)
    }
}

#[cfg(feature="unstable")]
impl<'a, T, R> Fn<(T,)> for Fix<'a, T, R> {
    #[inline]
    extern "rust-call" fn call(&self, x: (T,)) -> R {
        self.call(x.0)
    }
}

