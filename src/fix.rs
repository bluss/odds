use std::marker::PhantomData;

/// Fixpoint combinator for rust closures, generalized over the return type.
///
/// In **Fix\<F, T, R\>**, **T** is the argument type, and **R** is the return type,
/// **R** defaults to **T**.
///
/// Calling the `Fix` value only supports function call notation with the nightly
/// channel and the crate feature ‘unstable’ enabled; use the .call() method otherwise.
///
/// Use this best through the `fix` function.
///
/// ```
/// use odds::Fix;
/// use odds::fix;
///
/// let c = |f: Fix<_, i32>, x| if x == 0 { 1 } else { x * f.call(x - 1) };
/// let fact = Fix::new(&c);
/// assert_eq!(fact.call(5), 120);
///
/// let data = [true, false];
/// assert!(!fix(&data[..], |f, x| {
///     x.len() == 0 || x[0] && f.call(&x[1..])
/// }));
///
/// ```
#[cfg_attr(feature="unstable", doc="
```
// using feature `unstable`
use odds::Fix;

let c = |f: Fix<_, i32>, x| if x == 0 { 1 } else { x * f(x - 1) };
let fact = Fix::new(&c);
assert_eq!(fact(5), 120);
```
"
)]
pub struct Fix<'a, F: 'a, T: 'a, R: 'a = T>(&'a F, PhantomData<fn(T) -> R>);

impl<'a, F, T, R> Fix<'a, F, T, R>
    where F: Fn(Fix<F, T, R>, T) -> R,
{
    pub fn new(f: &'a F) -> Self {
        Fix(f, PhantomData)
    }
}

/// Fixpoint combinator for rust closures, generalized over the return type.
///
/// This is a wrapper function that uses the `Fix` type. The recursive closure
/// has two arguments, `Fix` and the argument type `T`.
///
/// In **Fix\<T, R\>**, **T** is the argument type, and **R** is the return type,
/// **R** defaults to **T**.
///
/// Calling the `Fix` value only supports function call notation with the nightly
/// channel and the crate feature ‘unstable’ enabled; use the .call() method otherwise.
///
/// This helper function makes the type inference work out well.
///
/// ```
/// use odds::fix;
/// 
/// assert_eq!(120, fix(5, |f, x| if x == 0 { 1 } else { x * f.call(x - 1) }));
///
/// let data = [true, false];
/// assert!(!fix(&data[..], |f, x| {
///     x.len() == 0 || x[0] && f.call(&x[1..])
/// }));
///
/// ```
#[cfg_attr(feature="unstable", doc="
```
// using feature `unstable`
use odds::fix;

assert_eq!(120, fix(5, |f, x| if x == 0 { 1 } else { x * f(x - 1) }));
```
"
)]
pub fn fix<T, R, F>(init: T, closure: F) -> R
    where F: Fn(Fix<F, T, R>, T) -> R
{
    Fix(&closure, PhantomData).call(init)
}

impl<'a, F, T, R> Fix<'a, F, T, R>
    where F: Fn(Fix<F, T, R>, T) -> R,
{
    pub fn call(&self, arg: T) -> R {
        let f = *self;
        f.0(f, arg)
    }
}

impl<'a, F, T, R> Clone for Fix<'a, F, T, R> {
    fn clone(&self) -> Self { *self }
}

impl<'a, F, T, R> Copy for Fix<'a, F, T, R> { }

#[cfg(feature="unstable")]
impl<'a, F, T, R> FnOnce<(T,)> for Fix<'a, F, T, R>
    where F: Fn(Fix<F, T, R>, T) -> R,
{
    type Output = R;
    #[inline]
    extern "rust-call" fn call_once(self, x: (T,)) -> R {
        self.call(x.0)
    }
}

#[cfg(feature="unstable")]
impl<'a, F, T, R> FnMut<(T,)> for Fix<'a, F, T, R>
    where F: Fn(Fix<F, T, R>, T) -> R,
{
    #[inline]
    extern "rust-call" fn call_mut(&mut self, x: (T,)) -> R {
        self.call(x.0)
    }
}

#[cfg(feature="unstable")]
impl<'a, F, T, R> Fn<(T,)> for Fix<'a, F, T, R>
    where F: Fn(Fix<F, T, R>, T) -> R,
{
    #[inline]
    extern "rust-call" fn call(&self, x: (T,)) -> R {
        self.call(x.0)
    }
}
