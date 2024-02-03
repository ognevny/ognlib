//! Some algorithms with power operations.

use std::ops::{Mul, MulAssign, Rem, RemAssign};

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

pub fn bin_pow<N>(mut b: N, mut e: u8) -> N
where N: MulAssign + From<u8> + Copy {
    let mut v = N::from(1);
    while e != 0 {
        if (e & 1) != 0 {
            v *= b
        }
        b *= b;
        e >>= 1;
    }
    v
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

pub fn modpow<N>(mut b: N, mut e: usize, m: N) -> N
where N: Mul<Output = N> + Rem<Output = N> + RemAssign + From<u8> + Copy + Eq {
    let mut result = N::from(1);
    b %= m;
    while e != 0 {
        if e & 1 == 1 {
            result = (result * b) % m;
        }
        e >>= 1;
        b = (b * b) % m;
    }
    result
}
