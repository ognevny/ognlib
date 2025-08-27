//! Primality tests. These tests are divided into 2 major groups: first group of tests gives exact
//! results; second group is for probabilistic tests, which can only suppose whether number is prime
//! or not.

#[cfg(feature = "std")] use rayon::prelude::*;

use {crate::num::power::modpow, fastrand::Rng, num_bigint::BigUint, thiserror::Error};

/// If number is less than 2, we can't say that number is either prime or composite.
#[non_exhaustive]
#[derive(Debug, Error, PartialEq, Eq, Clone, Copy)]
#[error("This number is neither prime nor composite")]
pub struct PrimeStatusError;

#[non_exhaustive]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum PrimeStatus {
    Prime,
    Composite,
    ProbablyPrime,
}

impl PrimeStatus {
    /// Returns `true` if [`PrimeStatus`] is [`Prime`].
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::{PrimeStatus, wilson_th};
    ///
    /// assert!(wilson_th(13usize).unwrap().is_prime());
    /// assert!(!wilson_th(455usize).unwrap().is_prime());
    /// ```
    ///
    /// [`Prime`]: PrimeStatus::Prime
    #[inline]
    #[must_use]
    pub fn is_prime(self) -> bool { self == Self::Prime }

    /// Returns `true` if [`PrimeStatus`] is not [`Composite`].
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::{PrimeStatus, miller_rabin};
    ///
    /// assert!(miller_rabin(13usize).unwrap().is_probably_prime());
    /// assert!(miller_rabin(7usize).unwrap().is_probably_prime());
    /// ```
    ///
    /// [`Composite`]: PrimeStatus::Composite
    #[inline]
    #[must_use]
    pub fn is_probably_prime(self) -> bool { self != Self::Composite }

    /// Returns `true` if [`PrimeStatus`] is [`Composite`].
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::{PrimeStatus, wilson_th};
    ///
    /// assert!(!wilson_th(13usize).unwrap().is_composite());
    /// assert!(wilson_th(455usize).unwrap().is_composite());
    /// ```
    ///
    /// [`Composite`]: PrimeStatus::Composite
    #[inline]
    #[must_use]
    pub fn is_composite(self) -> bool { self == Self::Composite }
}

/// Methods to check prime status.
pub trait Prime {
    /// Returns `true` if number is prime.
    fn is_prime(&self) -> bool;

    /// Returns `true` if number is either prime or probably prime.
    fn is_probably_prime(&self) -> bool;

    /// Returns `true` if number is composite.
    fn is_composite(&self) -> bool;
}

impl Prime for usize {
    /// Returns `true` if number is prime.
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::Prime;
    ///
    /// assert!(13usize.is_prime());
    /// assert!(!455usize.is_prime());
    /// ```
    #[inline]
    fn is_prime(&self) -> bool { wilson_th(*self) == Ok(PrimeStatus::Prime) }

    /// Returns `true` if number is either prime or probably prime.
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::Prime;
    ///
    /// assert!(13usize.is_probably_prime());
    /// assert!(7usize.is_probably_prime());
    /// ```
    #[inline]
    fn is_probably_prime(&self) -> bool { miller_rabin(*self) != Ok(PrimeStatus::Composite) }

    /// Returns `true` if number is composite.
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::Prime;
    ///
    /// assert!(!13usize.is_composite());
    /// assert!(455usize.is_composite());
    /// ```
    #[inline]
    fn is_composite(&self) -> bool { wilson_th(*self) == Ok(PrimeStatus::Composite) }
}

impl Prime for Result<PrimeStatus, PrimeStatusError> {
    /// Applied to result of prime test.
    ///
    /// Returns true if test is successful and value under result is [`PrimeStatus::Prime`].
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::{Prime, sqrtest};
    ///
    /// assert!(sqrtest(13).is_prime());
    /// assert!(!sqrtest(455).is_prime());
    /// ```
    #[inline]
    fn is_prime(&self) -> bool { self.is_ok_and(|st| st == PrimeStatus::Prime) }

    /// Applied to result of prime test.
    ///
    /// Returns true if test is successful and value under result is [`PrimeStatus::ProbablyPrime`].
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::{Prime, miller_rabin};
    ///
    /// assert!(miller_rabin(13).is_probably_prime());
    /// assert!(miller_rabin(7).is_probably_prime());
    /// ```
    #[inline]
    fn is_probably_prime(&self) -> bool { self.is_ok_and(|st| st == PrimeStatus::ProbablyPrime) }

    /// Applied to result of prime test.
    ///
    /// Returns true if test is successful and value under result is [`PrimeStatus::Composite`].
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::{Prime, sqrtest};
    ///
    /// assert!(!sqrtest(13).is_composite());
    /// assert!(sqrtest(455).is_composite());
    /// ```
    #[inline]
    fn is_composite(&self) -> bool { self.is_ok_and(|st| st == PrimeStatus::Composite) }
}

/// Simple prime test.
///
/// Prime test that takes ceil of sqrt(n) as upper bound and checks if there is any divisor from 3
/// to ceil with step 2.
///
/// # Errors
/// Returns a [`PrimeStatusError`] if number <= 1
///
/// # Examples
/// ```
/// use ognlib::algorithm::prime::{PrimeStatus, PrimeStatusError, sqrtest};
///
/// assert_eq!(sqrtest(1usize).unwrap_err().to_string(), "This number is neither prime nor composite");
/// assert_eq!(sqrtest(13usize).ok(), Some(PrimeStatus::Prime));
/// assert_eq!(sqrtest(455usize).ok(), Some(PrimeStatus::Composite));
/// ```
pub fn sqrtest(num: usize) -> Result<PrimeStatus, PrimeStatusError> {
    if num < 2 {
        Err(PrimeStatusError)
    } else {
        let sqrt_res = num.isqrt() + 1;
        cfg_if::cfg_if! {
            if #[cfg(feature = "std")] {
                let cond = (3..=sqrt_res).into_par_iter().find_any(|&i| num % i == 0).is_some();
            } else {
                let cond = (3..=sqrt_res).any(|i| num & i == 0);
            }
        };
        if cond { Ok(PrimeStatus::Composite) } else { Ok(PrimeStatus::Prime) }
    }
}

/// Wilson's theory.
///
/// From [Wikipedia](https://en.wikipedia.org/wiki/Wilson%27s_theorem): "Wilson's theorem states
/// that a natural number n > 1 is a prime number if and only if the product of all the positive
/// integers less than n is one less than a multiple of n. That is the factorial (n - 1)! satisfies
/// (n - 1)! % n == -1".
///
/// # Errors
/// Returns a [`PrimeStatusError`] if number <= 1
///
/// # Examples
/// ```
/// use ognlib::algorithm::prime::{PrimeStatus, PrimeStatusError, wilson_th};
///
/// assert_eq!(wilson_th(1usize).unwrap_err().to_string(), "This number is neither prime nor composite");
/// assert_eq!(wilson_th(13usize).ok(), Some(PrimeStatus::Prime));
/// assert_eq!(wilson_th(455usize).ok(), Some(PrimeStatus::Composite));
/// ```
pub fn wilson_th(num: usize) -> Result<PrimeStatus, PrimeStatusError> {
    if num < 2 {
        return Err(PrimeStatusError);
    }

    let mut fact = BigUint::from(1u8);
    for i in 2..num {
        fact = (fact * i) % num;
    }

    if fact + 1u8 == BigUint::from(num) { Ok(PrimeStatus::Prime) } else { Ok(PrimeStatus::Composite) }
}

/// Miller-Rabin's prime test.
///
/// From
/// [Wikipedia](https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test): the Miller–Rabin
/// primality test or Rabin–Miller primality test is a probabilistic primality test: an algorithm
/// which determines whether a given number is likely to be prime.
///
/// NOTE:
/// This function is *not* cryptographically safe
///
/// # Errors
/// Returns a [`PrimeStatusError`] if number <= 1
///
/// # Examples
/// ```
/// use ognlib::algorithm::prime::{PrimeStatus, PrimeStatusError, miller_rabin};
///
/// assert_eq!(miller_rabin(1usize).unwrap_err().to_string(), "This number is neither prime nor composite");
/// assert_eq!(miller_rabin(13usize).ok(), Some(PrimeStatus::ProbablyPrime));
/// assert_eq!(miller_rabin(455usize).ok(), Some(PrimeStatus::Composite));
/// ```
pub fn miller_rabin(num: usize) -> Result<PrimeStatus, PrimeStatusError> {
    match num {
        0 | 1 => Err(PrimeStatusError),
        5 => Ok(PrimeStatus::Prime),
        _ if num % 2 == 0 || num % 3 == 0 => Ok(PrimeStatus::Composite),
        _ => {
            let log_sqr = (num.ilog2() * num.ilog2()).into();
            let (mut temp, mut su) = (num - 1, 0);
            while temp % 2 == 0 {
                temp /= 2;
                su += 1;
            }
            'outer: for i in 0..log_sqr {
                let rand_num = Rng::with_seed(i).usize(2..num - 1);
                let mut x_num = modpow(rand_num, temp, num);
                if x_num == 1 || x_num == num - 1 {
                    continue;
                }
                for _j in 0..su - 1 {
                    x_num = modpow(x_num, 2, num);
                    if x_num == 1 {
                        return Ok(PrimeStatus::Composite);
                    }
                    if x_num == num - 1 {
                        continue 'outer;
                    }
                }
                return Ok(PrimeStatus::Composite);
            }
            Ok(PrimeStatus::ProbablyPrime)
        },
    }
}
