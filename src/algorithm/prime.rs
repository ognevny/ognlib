//! Primality tests. These tests are divided into 2 major groups: first group of tests gives exact
//! results; second group is for probabilistic tests, which can only suppose whether number is prime
//! or not.

use {rayon::prelude::*, thiserror::Error};

/// If number is less than 2, we can't say that number is either prime or composite.
#[derive(Debug, Error, PartialEq)]
#[error("This number is neither prime nor composite")]
pub struct PrimeStatusError;

#[derive(Debug, PartialEq)]
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
    /// use ognlib::algorithm::prime::{sqrtest, PrimeStatus};
    ///
    /// assert!(sqrtest(13).unwrap().is_prime());
    /// assert!(!sqrtest(455).unwrap().is_prime());
    /// ```
    ///
    /// [`Prime`]: PrimeStatus::Prime
    #[inline]
    pub fn is_prime(self) -> bool { self == PrimeStatus::Prime }

    /// Returns `true` if [`PrimeStatus`] is not [`Composite`].
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::{miller_rabin, PrimeStatus};
    ///
    /// assert!(miller_rabin(13).unwrap().is_probably_prime());
    /// assert!(miller_rabin(7).unwrap().is_probably_prime());
    /// ```
    ///
    /// [`Composite`]: PrimeStatus::Composite
    #[inline]
    pub fn is_probably_prime(self) -> bool { self != PrimeStatus::Composite }

    /// Returns `true` if [`PrimeStatus`] is [`Composite`].
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::{sqrtest, PrimeStatus};
    ///
    /// assert!(!sqrtest(13).unwrap().is_composite());
    /// assert!(sqrtest(455).unwrap().is_composite());
    /// ```
    ///
    /// [`Composite`]: PrimeStatus::Composite
    #[inline]
    pub fn is_composite(self) -> bool { self == PrimeStatus::Composite }
}

/// Methods to check prime status.
pub trait Prime {
    #[cfg(feature = "num-bigint")]
    /// Returns `true` if number is prime.
    fn is_prime(&self) -> bool;

    /// Returns `true` if number is either prime or probably prime.
    fn is_probably_prime(&self) -> bool;
    #[cfg(feature = "num-bigint")]
    /// Returns `true` if number is composite.
    fn is_composite(&self) -> bool;
}

impl Prime for isize {
    /// Returns `true` if number is prime.
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::Prime;
    ///
    /// assert!(13.is_prime());
    /// assert!(!455.is_prime());
    /// ```
    #[cfg(feature = "num-bigint")]
    #[inline]
    fn is_prime(&self) -> bool { wilson_th(*self) == Ok(PrimeStatus::Prime) }

    /// Returns `true` if number is either prime or probably prime.
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::Prime;
    ///
    /// assert!(13.is_probably_prime());
    /// assert!(7.is_probably_prime());
    /// ```
    #[inline]
    fn is_probably_prime(&self) -> bool { miller_rabin(*self) != Ok(PrimeStatus::Composite) }

    /// Returns `true` if number is composite.
    /// # Examples
    ///
    /// ```
    /// use ognlib::algorithm::prime::Prime;
    ///
    /// assert!(!13.is_composite());
    /// assert!(455.is_composite());
    /// ```
    #[cfg(feature = "num-bigint")]
    #[inline]
    fn is_composite(&self) -> bool { wilson_th(*self) == Ok(PrimeStatus::Composite) }
}

/// Prime test that takes ceil of sqrt(n) as upper bound and checks if there is any divisor from 3
/// to ceil with step 2.
///
/// # Examples
/// ```
/// use ognlib::algorithm::prime::{sqrtest, PrimeStatus, PrimeStatusError};
///
/// assert_eq!(sqrtest(1).unwrap_err().to_string(), "This number is neither prime nor composite",);
/// assert_eq!(sqrtest(13).ok(), Some(PrimeStatus::Prime));
/// assert_eq!(sqrtest(455).ok(), Some(PrimeStatus::Composite));
/// ```

pub fn sqrtest(n: isize) -> Result<PrimeStatus, PrimeStatusError> {
    match n {
        ..=1 => Err(PrimeStatusError),
        _ => {
            if (3..=(n as f64).sqrt().ceil() as usize)
                .into_par_iter()
                .find_any(|&i| n as usize % i == 0)
                .is_some()
            {
                Ok(PrimeStatus::Composite)
            } else {
                Ok(PrimeStatus::Prime)
            }
        },
    }
}

/// Wilson's theory. From [Wikipedia](https://en.wikipedia.org/wiki/Wilson%27s_theorem): "Wilson's
/// theorem states that a natural number n > 1 is a prime number if and only if the product of all
/// the positive integers less than n is one less than a multiple of n. That is the factorial
/// (n - 1)! satisfies (n - 1)! % n == -1".
///
/// # Examples
/// ```
/// use ognlib::algorithm::prime::{wilson_th, PrimeStatus, PrimeStatusError};
///
/// assert_eq!(
///     wilson_th(1).unwrap_err().to_string(),
///     "This number is neither prime nor composite",
/// );
/// assert_eq!(wilson_th(13).ok(), Some(PrimeStatus::Prime));
/// assert_eq!(wilson_th(455).ok(), Some(PrimeStatus::Composite));
/// ```
#[cfg(feature = "num-bigint")]
pub fn wilson_th(n: isize) -> Result<PrimeStatus, PrimeStatusError> {
    use num_bigint::BigInt;

    if n < 2 {
        return Err(PrimeStatusError);
    }

    let mut fact = BigInt::from(1);
    for i in 2..n {
        fact = (fact * i) % n;
    }

    if fact + 1 == BigInt::from(n) { Ok(PrimeStatus::Prime) } else { Ok(PrimeStatus::Composite) }
}

/// Miller-Rabin's prime test. From
/// [Wikipedia](https://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test): the Miller–Rabin
/// primality test or Rabin–Miller primality test is a probabilistic primality test: an algorithm
/// which determines whether a given number is likely to be prime.
///
/// # Examples
/// ```
/// use ognlib::algorithm::prime::{miller_rabin, PrimeStatus, PrimeStatusError};
///
/// assert_eq!(
///     miller_rabin(1).unwrap_err().to_string(),
///     "This number is neither prime nor composite",
/// );
/// assert_eq!(miller_rabin(13).ok(), Some(PrimeStatus::ProbablyPrime));
/// assert_eq!(miller_rabin(455).ok(), Some(PrimeStatus::Composite));
/// ```

pub fn miller_rabin(n: isize) -> Result<PrimeStatus, PrimeStatusError> {
    use {crate::num::power::modpow, rand::Rng};

    match n {
        ..=1 => Err(PrimeStatusError),
        5 => Ok(PrimeStatus::Prime),
        _ if n % 2 == 0 || n % 3 == 0 => Ok(PrimeStatus::Composite),
        _ => {
            let k = ((n as f64).log2().ceil() * (n as f64).log2().ceil()) as isize;
            let (mut t, mut s) = (n - 1, 0);
            while t % 2 == 0 {
                t /= 2;
                s += 1;
            }
            'outer: for _i in 0..k {
                let a = rand::thread_rng().gen_range(2..n - 1);
                let mut x = modpow(a, t as usize, n);
                if x == 1 || x == n - 1 {
                    continue;
                }
                for _j in 0..s - 1 {
                    x = modpow(x, 2, n);
                    if x == 1 {
                        return Ok(PrimeStatus::Composite);
                    }
                    if x == n - 1 {
                        continue 'outer;
                    }
                }
                return Ok(PrimeStatus::Composite);
            }
            Ok(PrimeStatus::ProbablyPrime)
        },
    }
}
