//! Some algorithms with power operations.

use core::ops::{BitAnd, Mul, MulAssign, Rem, RemAssign, ShrAssign};

/// Algorithm for binary power. Due to fact that returned value has the same type as base, it could
/// fail with overflowing.
/// # Examples
///
/// ```
/// use ognlib::num::power::bin_pow;
///
/// assert_eq!(bin_pow(123, 3), 1860867);
/// assert_eq!(bin_pow(0.5, 4), 0.0625);
/// ```
pub fn bin_pow<N>(mut base: N, mut exp: u8) -> N
where N: MulAssign + From<u8> + Copy {
    let mut vi = N::from(1);
    while exp != 0 {
        if (exp & 1) != 0 {
            vi *= base;
        }
        base *= base;
        exp >>= 1;
    }
    vi
}

/// Modular exponentation.
/// # Examples
///
/// ```
/// use ognlib::num::power::modpow;
///
/// let mod1 = modpow(2, 3, 5);
/// let mod2 = modpow(5, 4, 3);
///
/// assert_eq!(mod1, 3);
/// assert_eq!(mod2, 1);
/// ```
pub fn modpow<N>(mut base: N, mut exp: N, modulo: N) -> N
where N: Mul<Output = N>
        + Rem<Output = N>
        + RemAssign
        + From<u8>
        + Copy
        + Eq
        + BitAnd<Output = N>
        + ShrAssign<i32> {
    let mut res = 1.into();
    base %= modulo;
    while exp != 0.into() {
        if exp & 1.into() == 1.into() {
            res = (res * base) % modulo;
        }
        exp >>= 1;
        base = (base * base) % modulo;
    }
    res
}
