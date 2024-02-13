//! Structs for radix numbers (String nums and int nums). All numbers are unsigned integers.

use {
    std::{cmp::Ordering, num::ParseIntError, ops, str::FromStr},
    thiserror::Error,
};

/// Reference to slice of chars from '0' to 'Z' (maximum base is 36).
pub const RADIX: &[char] = &[
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I',
    'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
];

/// Translate [`Radix`] or [`StringRadix`], `integer` or [`String`] number from given base into a
/// [`usize`] dec number.
/// # Examples
///
/// ```
/// use ognlib::{
///     dec,
///     num::radix::{Radix, StringRadix},
/// };
///
/// let n = Radix::from_radix(444, 8).unwrap();
/// let n_str = StringRadix::from_radix("444", 8).unwrap();
///
/// assert_eq!(dec!(n), 292);
/// assert_eq!(dec!(n_str), 292);
///
/// assert_eq!(dec!(444, 8), 292);
/// assert_eq!(dec!("444", 8), 292);
/// ```
#[macro_export]
macro_rules! dec {
    ($radix:expr) => {
        Into::<usize>::into($radix)
    };
    ($num:expr, $base:expr) => {
        usize::from_str_radix(&$num.to_string(), $base).unwrap()
    };
}

/// You can have 2 problems with radix numbers: first, base could be incorrect when it's not in
/// range `2..=10` for [`Radix`] or `2..=36` for [`StringRadix`]; second, number can be incorrect,
/// as number contains digits that are more or equal than base. Also there is can be convertsion
/// error, which is just [`ParseIntError`] from std.
///
/// [`ParseIntError`]: std::num::ParseIntError
#[non_exhaustive]
#[derive(Debug, Error, PartialEq, Eq)]
pub enum RadixError {
    #[error("Expected base in range `2..={0}`, found {1}")]
    BaseError(u8, u8),
    #[error("Number contains a digit ({0}) that is more or equal than base ({1})")]
    NumberError(char, u8),
    #[error(transparent)]
    ParseError(#[from] ParseIntError),
}

/// Radix number, that is usually written as *number*<sub>*base*</sub> (444<sub>8</sub> for
/// example). Base can be only in range `2..=10`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Radix {
    /// a number of radix number
    number: usize,

    /// a base of radix number
    base: u8,
}

impl FromStr for Radix {
    type Err = ParseIntError;

    /// Creates a new [`Radix`] with base 10 and given [`str`] number.
    ///
    /// # Errors
    /// Returns [`ParseIntError`] if number contains invalid digits.
    ///
    /// [`ParseIntError`]: std::num::ParseIntError
    ///
    /// # Examples
    ///
    /// ```
    /// use {ognlib::num::radix::Radix, std::str::FromStr};
    ///
    /// let n = Radix::from_str("123").unwrap();
    /// assert_eq!(n.radix(), (123, 10));
    ///
    /// let e = Radix::from_str("12A").unwrap_err();
    /// assert_eq!(e.to_string(), "invalid digit found in string");
    /// ```
    #[inline]
    fn from_str(number: &str) -> Result<Self, Self::Err> {
        Ok(Self { number: number.parse()?, base: 10 })
    }
}

/// Radix number, that is usually written as *number*<sub>*base*</sub> (444<sub>8</sub> for
/// example), but number is represented as [`String`] so base could be from range `2..=36`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringRadix {
    /// a number of radix represented as [`String`]
    number: String,

    /// a base of radix number
    base: u8,
}

impl FromStr for StringRadix {
    type Err = ParseIntError;

    /// Creates a new [`StringRadix`] with base 10 and given [`str`] number.
    ///
    /// # Errors
    /// Returns [`ParseIntError`] if number contains invalid digit.
    ///
    /// [`ParseIntError`]: std::num::ParseIntError
    ///
    /// # Examples
    ///
    /// ```
    /// use {ognlib::num::radix::StringRadix, std::str::FromStr};
    ///
    /// let n = StringRadix::from_str("123").unwrap();
    /// assert_eq!(n.radix(), ("123", 10));
    ///
    /// let e = StringRadix::from_str("12A").unwrap_err();
    /// assert_eq!(e.to_string(), "invalid digit found in string");
    /// ```
    #[inline]
    fn from_str(number: &str) -> Result<Self, Self::Err> {
        Ok(Self { number: number.parse::<usize>()?.to_string(), base: 10 })
    }
}

/// impl common traits for radix structs
macro_rules! impl_traits {
    ($($radix:ident)*) => {
        $(impl PartialOrd for $radix {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }
        }
        impl Ord for $radix {
            fn cmp(&self, other: &Self) -> Ordering {
                dec!(self).cmp(&dec!(other))
            }
        }
        impl ops::Add for $radix {
            type Output = Self;

            /// Performs a `+` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n1 = Radix::from_radix(123, 4).unwrap();
            /// let n2 = Radix::from_radix(444, 5).unwrap();
            /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
            /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// let res = (n1 + n2).to_radix(8).unwrap();
            /// let res_str = (n_str1 + n_str2).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (227, 8));
            /// assert_eq!(res_str.radix(), ("227", 8));
            /// ```
            fn add(self, other: Self) -> Self::Output {
                Self {
                    number: Self::from(dec!(&self) + dec!(&other))
                        .to_radix(self.base)
                        .unwrap()
                        .number,
                    base: self.base,
                }
            }
        }
        impl ops::Add<usize> for $radix {
            type Output = Self;

            /// Performs a `+` operation ([`usize`] as `rhs`).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n = Radix::from_radix(123, 4).unwrap();
            /// let n_str = StringRadix::from_radix("123", 4).unwrap();
            ///
            /// let res = (n + 124).to_radix(8).unwrap();
            /// let res_str = (n_str + 124).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (227, 8));
            /// assert_eq!(res_str.radix(), ("227", 8));
            /// ```
            fn add(self, other: usize) -> Self::Output {
                Self {
                    number: Self::from(dec!(&self) + other)
                        .to_radix(self.base)
                        .unwrap()
                        .number,
                    base: self.base,
                }
            }
        }
        impl ops::AddAssign for $radix {
            /// Performs a `+=` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let mut n1 = Radix::from_radix(123, 4).unwrap();
            /// let n2 = Radix::from_radix(444, 5).unwrap();
            /// let mut n_str1 = StringRadix::from_radix("123", 4).unwrap();
            /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// n1 += n2;
            /// n_str1 += n_str2;
            ///
            /// n1 = n1.to_radix(8).unwrap();
            /// n_str1 = n_str1.to_radix(8).unwrap();
            ///
            /// assert_eq!(n1.radix(), (227, 8));
            /// assert_eq!(n_str1.radix(), ("227", 8));
            /// ```
            fn add_assign(&mut self, other: Self) {
                *self = self.clone() + other
            }
        }
        impl ops::AddAssign<usize> for $radix {
            /// Performs a `+=` operation ([`usize`] is rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let mut n = Radix::from_radix(123, 4).unwrap();
            /// let mut n_str = StringRadix::from_radix("123", 4).unwrap();
            ///
            /// n += 124;
            /// n_str += 124;
            ///
            /// n = n.to_radix(8).unwrap();
            /// n_str = n_str.to_radix(8).unwrap();
            ///
            /// assert_eq!(n.radix(), (227, 8));
            /// assert_eq!(n_str.radix(), ("227", 8));
            /// ```
            fn add_assign(&mut self, other: usize) {
                *self = self.clone() + Self::from(other)
            }
        }
        impl ops::Sub for $radix {
            type Output = Self;

            /// Performs a `-` operation. Result of the operation is an absolute value. Base of the
            /// resulting number is the base of the greater number.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n1 = Radix::from_radix(123, 4).unwrap();
            /// let n2 = Radix::from_radix(444, 5).unwrap();
            /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
            /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// let res = (n1 - n2).to_radix(8).unwrap();
            /// let res_str = (n_str1 - n_str2).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (141, 8));
            /// assert_eq!(res_str.radix(), ("141", 8));
            /// ```
            fn sub(self, other: Self) -> Self::Output {
                if self > other {
                    Self {
                        number: Self::from(dec!(&self) - dec!(&other))
                            .to_radix(self.base)
                            .unwrap()
                            .number,
                        base: self.base,
                    }
                } else {
                    Self {
                        number: Self::from(dec!(&other) - dec!(&self))
                            .to_radix(other.base)
                            .unwrap()
                            .number,
                        base: other.base,
                    }
                }
            }
        }
        impl ops::Sub<usize> for $radix {
            type Output = Self;

            /// Performs a `-` operation ([`usize`] is rhs). Result of operation is an absolute
            /// value. Base of resulting number is the base of greater number.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n = Radix::from_radix(123, 4).unwrap();
            /// let n_str = StringRadix::from_radix("123", 4).unwrap();
            ///
            /// let res = (n - 124).to_radix(8).unwrap();
            /// let res_str = (n_str - 124).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (141, 8));
            /// assert_eq!(res_str.radix(), ("141", 8));
            /// ```
            fn sub(self, other: usize) -> Self::Output {
                if self > Self::from(other) {
                    Self {
                        number: Self::from(dec!(&self) - other)
                            .to_radix(self.base)
                            .unwrap()
                            .number,
                        base: self.base,
                    }
                } else {
                    Self {
                        number: Self::from(other - dec!(self))
                            .to_radix(10)
                            .unwrap()
                            .number,
                        base: 10,
                    }
                }
            }
        }
        impl ops::SubAssign for $radix {
            /// Performs a `-=` operation. The same rules as [`Sub`] are applied.
            ///
            /// [`Sub`]: Radix::Sub
            ///
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let mut n1 = Radix::from_radix(123, 4).unwrap();
            /// let n2 = Radix::from_radix(444, 5).unwrap();
            /// let mut n_str1 = StringRadix::from_radix("123", 4).unwrap();
            /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// n1 -= n2;
            /// n_str1 -= n_str2;
            ///
            /// n1 = n1.to_radix(8).unwrap();
            /// n_str1 = n_str1.to_radix(8).unwrap();
            ///
            /// assert_eq!(n1.radix(), (141, 8));
            /// assert_eq!(n_str1.radix(), ("141", 8));
            /// ```
            fn sub_assign(&mut self, other: Self) {
                *self = self.clone() - other;
            }
        }
        impl ops::SubAssign<usize> for $radix {
            /// Performs a `-=` operation ([`usize`] as rhs). The same rules as [`Sub`] are applied.
            ///
            /// [`Sub`]: Radix::Sub
            ///
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let mut n = Radix::from_radix(123, 4).unwrap();
            /// let mut n_str = StringRadix::from_radix("123", 4).unwrap();
            ///
            /// n -= 124;
            /// n_str -= 124;
            ///
            /// n = n.to_radix(8).unwrap();
            /// n_str = n_str.to_radix(8).unwrap();
            ///
            /// assert_eq!(n.radix(), (141, 8));
            /// assert_eq!(n_str.radix(), ("141", 8));
            /// ```
            fn sub_assign(&mut self, other: usize) {
                *self = self.clone() - other;
            }
        }
        impl ops::Mul for $radix {
            type Output = Self;

            /// Performs a `*` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n1 = Radix::from_radix(123, 4).unwrap();
            /// let n2 = Radix::from_radix(444, 5).unwrap();
            /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
            /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// let res = (n1 * n2).to_radix(8).unwrap();
            /// let res_str = (n_str1 * n_str2).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (6424, 8));
            /// assert_eq!(res_str.radix(), ("6424", 8));
            /// ```
            fn mul(self, other: Self) -> Self::Output {
                Self {
                    number: Self::from(dec!(&self) * dec!(&other))
                        .to_radix(self.base)
                        .unwrap()
                        .number,
                    base: self.base,
                }
            }
        }
        impl ops::Mul<usize> for $radix {
            type Output = Self;

            /// Performs a `*` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n = Radix::from_radix(123, 4).unwrap();
            /// let n_str = StringRadix::from_radix("123", 4).unwrap();
            ///
            /// let res = (n * 124).to_radix(8).unwrap();
            /// let res_str = (n_str * 124).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (6424, 8));
            /// assert_eq!(res_str.radix(), ("6424", 8));
            /// ```
            fn mul(self, other: usize) -> Self::Output {
                Self {
                    number: Self::from(dec!(&self) * other)
                        .to_radix(self.base)
                        .unwrap()
                        .number,
                    base: self.base,
                }
            }
        }
        impl ops::MulAssign for $radix {
            /// Performs a `*=` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let mut n1 = Radix::from_radix(123, 4).unwrap();
            /// let n2 = Radix::from_radix(444, 5).unwrap();
            /// let mut n_str1 = StringRadix::from_radix("123", 4).unwrap();
            /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// n1 *= n2;
            /// n_str1 *= n_str2;
            ///
            /// n1 = n1.to_radix(8).unwrap();
            /// n_str1 = n_str1.to_radix(8).unwrap();
            ///
            /// assert_eq!(n1.radix(), (6424, 8));
            /// assert_eq!(n_str1.radix(), ("6424", 8));
            /// ```
            fn mul_assign(&mut self, other: Self) {
                *self = self.clone() * other;
            }
        }
        impl ops::MulAssign<usize> for $radix {
            /// Performs a `*=` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let mut n = Radix::from_radix(123, 4).unwrap();
            /// let mut n_str = StringRadix::from_radix("123", 4).unwrap();
            ///
            /// n *= 124;
            /// n_str *= 124;
            ///
            /// n = n.to_radix(8).unwrap();
            /// n_str = n_str.to_radix(8).unwrap();
            ///
            /// assert_eq!(n.radix(), (6424, 8));
            /// assert_eq!(n_str.radix(), ("6424", 8));
            /// ```
            fn mul_assign(&mut self, other: usize) {
                *self = self.clone() * other;
            }
        }
        impl ops::Div for $radix {
            type Output = Self;

            /// Performs a `/` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n1 = Radix::from_radix(123, 4).unwrap();
            /// let n2 = Radix::from_radix(444, 5).unwrap();
            /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
            /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// let res = (n2 / n1).to_radix(8).unwrap();
            /// let res_str = (n_str2 / n_str1).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (4, 8));
            /// assert_eq!(res_str.radix(), ("4", 8));
            /// ```
            fn div(self, other: Self) -> Self::Output {
                Self {
                    number: Self::from(dec!(&self) / dec!(&other))
                        .to_radix(self.base)
                        .unwrap()
                        .number,
                    base: self.base,
                }
            }
        }
        impl ops::Div<usize> for $radix {
            type Output = Self;

            /// Performs a `/` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n = Radix::from_radix(444, 5).unwrap();
            /// let n_str = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// let res = (n / 27).to_radix(8).unwrap();
            /// let res_str = (n_str / 27).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (4, 8));
            /// assert_eq!(res_str.radix(), ("4", 8));
            /// ```
            fn div(self, other: usize) -> Self::Output {
                Self {
                    number: Self::from(dec!(&self) / other)
                        .to_radix(self.base)
                        .unwrap()
                        .number,
                    base: self.base,
                }
            }
        }
        impl ops::DivAssign for $radix {
            /// Performs a `/=` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n1 = Radix::from_radix(123, 4).unwrap();
            /// let mut n2 = Radix::from_radix(444, 5).unwrap();
            /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
            /// let mut n_str2 = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// n2 /= n1;
            /// n_str2 /= n_str1;
            ///
            /// n2 = n2.to_radix(8).unwrap();
            /// n_str2 = n_str2.to_radix(8).unwrap();
            ///
            /// assert_eq!(n2.radix(), (4, 8));
            /// assert_eq!(n_str2.radix(), ("4", 8));
            /// ```
            fn div_assign(&mut self, other: Self) {
                *self = self.clone() / other;
            }
        }
        impl ops::DivAssign<usize> for $radix {
            /// Performs a `/=` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let mut n = Radix::from_radix(444, 5).unwrap();
            /// let mut n_str = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// n /= 27;
            /// n_str /= 27;
            ///
            /// n = n.to_radix(8).unwrap();
            /// n_str = n_str.to_radix(8).unwrap();
            ///
            /// assert_eq!(n.radix(), (4, 8));
            /// assert_eq!(n_str.radix(), ("4", 8));
            /// ```
            fn div_assign(&mut self, other: usize) {
                *self = self.clone() / other;
            }
        }
        impl ops::Rem for $radix {
            type Output = Self;

            /// Performs a `%` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n1 = Radix::from_radix(123, 4).unwrap();
            /// let n2 = Radix::from_radix(444, 5).unwrap();
            /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
            /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// let res = (n2 % n1).to_radix(8).unwrap();
            /// let res_str = (n_str2 % n_str1).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (20, 8));
            /// assert_eq!(res_str.radix(), ("20", 8));
            /// ```
            fn rem(self, other: Self) -> Self::Output {
                Self {
                    number: Self::from(dec!(&self) % dec!(&other))
                        .to_radix(self.base)
                        .unwrap()
                        .number,
                    base: self.base,
                }
            }
        }
        impl ops::Rem<usize> for $radix {
            type Output = Self;

            /// Performs a `%` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n = Radix::from_radix(444, 5).unwrap();
            /// let n_str = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// let res = (n % 27).to_radix(8).unwrap();
            /// let res_str = (n_str % 27).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (20, 8));
            /// assert_eq!(res_str.radix(), ("20", 8));
            /// ```
            fn rem(self, other: usize) -> Self::Output {
                Self {
                    number: Self::from(dec!(&self) % other)
                        .to_radix(self.base)
                        .unwrap()
                        .number,
                    base: self.base,
                }
            }
        }
        impl ops::RemAssign for $radix {
            /// Performs a `%=` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n1 = Radix::from_radix(123, 4).unwrap();
            /// let mut n2 = Radix::from_radix(444, 5).unwrap();
            /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
            /// let mut n_str2 = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// n2 %= n1;
            /// n_str2 %= n_str1;
            ///
            /// n2 = n2.to_radix(8).unwrap();
            /// n_str2 = n_str2.to_radix(8).unwrap();
            ///
            /// assert_eq!(n2.radix(), (20, 8));
            /// assert_eq!(n_str2.radix(), ("20", 8));
            /// ```
            fn rem_assign(&mut self, other: Self) {
                *self = self.clone() % other;
            }
        }
        impl ops::RemAssign<usize> for $radix {
            /// Performs a `%=` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let mut n = Radix::from_radix(444, 5).unwrap();
            /// let mut n_str = StringRadix::from_radix("444", 5).unwrap();
            ///
            /// n %= 27;
            /// n_str %= 27;
            ///
            /// n = n.to_radix(8).unwrap();
            /// n_str = n_str.to_radix(8).unwrap();
            ///
            /// assert_eq!(n.radix(), (20, 8));
            /// assert_eq!(n_str.radix(), ("20", 8));
            /// ```
            fn rem_assign(&mut self, other: usize) {
                *self = self.clone() % other;
            }
        })*
    };
}

/// impl some common From traits for radix
macro_rules! impl_froms {
    ($($type:ty)*) => {
        $(impl From<$type> for Radix {
            /// Creates a new [`Radix`] with base 10 and given integer number.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let radix = Radix::from(123);
            /// assert_eq!(radix.number(), 123);
            /// assert_eq!(radix.base(), 10);
            /// ```
            #[inline]
            fn from(number: $type) -> Self {
                Self {
                    number: number as usize,
                    base: 10,
                }
            }
        }
        impl From<$type> for StringRadix {
            /// Creates a new [`StringRadix`] with base 10 and given integer number.
            ///
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let radix = StringRadix::from(123);
            /// assert_eq!(radix.number(), "123");
            /// assert_eq!(radix.base(), 10);
            #[inline]
            fn from(number: $type) -> Self {
                Self {
                    number: number.to_string(),
                    base: 10,
                }
            }
        }
        impl From<Radix> for $type {
            /// Converts a [`Radix`] into primitive int.
            ///
            /// # Example
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let radix = Radix::from_radix(444, 5).unwrap();
            /// let num: usize = radix.into();
            ///
            /// assert_eq!(num, 124);
            /// ```
            #[inline]
            fn from(radix: Radix) -> Self {
                Self::from_str_radix(&radix.number.to_string(), radix.base.into()).unwrap()
            }
        }
        impl From<StringRadix> for $type {
            /// Converts a [`StringRadix`] into primitive int.
            ///
            /// # Example
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let radix = StringRadix::from_radix("444", 5).unwrap();
            /// let num: usize = radix.into();
            ///
            /// assert_eq!(num, 124);
            /// ```
            #[inline]
            fn from(radix: StringRadix) -> Self {
                Self::from_str_radix(&radix.number, radix.base.into()).unwrap()
            }
        }
        impl From<&Radix> for $type {
            /// Converts a [`Radix`] into primitive int.
            ///
            /// # Example
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let radix = Radix::from_radix(444, 5).unwrap();
            /// let num: usize = radix.into();
            ///
            /// assert_eq!(num, 124);
            /// ```
            #[inline]
            fn from(radix: &Radix) -> Self {
                Self::from_str_radix(&radix.number.to_string(), radix.base.into()).unwrap()
            }
        }
        impl From<&StringRadix> for $type {
            /// Converts a [`StringRadix`] into primitive int.
            ///
            /// # Example
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let radix = StringRadix::from_radix("444", 5).unwrap();
            /// let num: usize = radix.into();
            ///
            /// assert_eq!(num, 124);
            /// ```
            #[inline]
            fn from(radix: &StringRadix) -> Self {
                Self::from_str_radix(&radix.number, radix.base.into()).unwrap()
            }
        })*
    };
}

impl_traits!(Radix StringRadix);
impl_froms!(i8 i16 i32 i64 isize u8 u16 u32 u64 usize);

impl Radix {
    /// Creates a new [`Radix`].
    ///
    /// # Errors
    /// Returns a [`BaseError`] when base isn't correct.
    ///
    /// [`BaseError`]: RadixError::BaseError
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let n = Radix::new(2).unwrap();
    /// assert_eq!(n.number(), 0);
    /// assert_eq!(n.base(), 2);
    ///
    /// let e1 = Radix::new(1).unwrap_err();
    /// assert_eq!(e1.to_string(), "Expected base in range `2..=10`, found 1");
    ///
    /// let e2 = Radix::new(33).unwrap_err();
    /// assert_eq!(e2.to_string(), "Expected base in range `2..=10`, found 33");
    /// ```
    pub const fn new(base: u8) -> Result<Self, RadixError> {
        match base {
            0 | 1 | 11.. => Err(RadixError::BaseError(10, base)),
            _ => Ok(Self { number: 0, base }),
        }
    }

    /// Creates a new [`Radix`] with given number and base.
    ///
    /// # Errors
    /// Returns a [`BaseError`] if base isn't correct; [`NumberError`] if number isn't correct.
    ///
    /// [`BaseError`]: RadixError::BaseError
    /// [`NumberError`]: RadixError::NumberError
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let n = Radix::from_radix(11010000, 2).unwrap();
    /// assert_eq!(n.number(), 11010000);
    /// assert_eq!(n.base(), 2);
    ///
    /// let e = Radix::from_radix(444, 3).unwrap_err();
    /// assert_eq!(e.to_string(), "Number contains a digit (4) that is more or equal than base (3)",);
    /// ```
    pub fn from_radix(number: usize, base: u8) -> Result<Self, RadixError> {
        match base {
            0 | 1 | 11.. => Err(RadixError::BaseError(10, base)),
            _ => {
                use super::methods::Num;

                RADIX
                    .iter()
                    .take(10)
                    .skip(base.into())
                    .find_map(|i| {
                        number
                            .has_digit(i.to_string().parse().unwrap())
                            .then_some(Err(RadixError::NumberError(*i, base)))
                    })
                    .map_or(Ok(Self { number, base }), |err| err)
            },
        }
    }

    /// Returns a number of [`Radix`].
    ///
    /// # Example
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let radix = Radix::from_radix(444, 5).unwrap();
    ///
    /// assert_eq!(radix.number(), 444);
    /// ```
    #[inline]
    #[must_use]
    pub const fn number(&self) -> usize { self.number }

    /// Returns a base of [`Radix`].
    ///
    /// # Example
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let radix = Radix::from_radix(444, 5).unwrap();
    ///
    /// assert_eq!(radix.base(), 5);
    /// ```
    #[inline]
    #[must_use]
    pub const fn base(&self) -> u8 { self.base }

    /// Returns a full [`Radix`] as tuple (number, base).
    ///
    /// # Example
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let radix = Radix::from_radix(444, 5).unwrap();
    ///
    /// assert_eq!(radix.radix(), (444, 5));
    /// ```
    #[inline]
    #[must_use]
    pub const fn radix(&self) -> (usize, u8) { (self.number, self.base) }

    /// Translate [`Radix`] to another [`Radix`].
    ///
    /// # Panics
    /// Panics if k is less than 2 or k more than 36.
    ///
    /// # Errors
    /// Returns a [`BaseError`] when base isn't correct; [`ParseError`] if there was error with
    /// parse functions.
    ///
    /// [`BaseError`]: RadixError::BaseError
    /// [`ParseError`]: RadixError::ParseError
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let n1 = Radix::from(123);
    /// let new1 = n1.to_radix(8).unwrap();
    ///
    /// let n2 = Radix::from_radix(173, 8).unwrap();
    /// let new2 = n2.to_radix(10).unwrap();
    ///
    /// assert_eq!(new1.radix(), (173, 8));
    /// assert_eq!(new2.radix(), (123, 10));
    ///
    /// let e = new2.to_radix(1).unwrap_err();
    /// assert_eq!(e.to_string(), "Expected base in range `2..=10`, found 1");
    /// ```
    pub fn to_radix(self, base: u8) -> Result<Self, RadixError> {
        match base {
            0 | 1 | 11.. => Err(RadixError::BaseError(10, base)),
            10 => Ok(self.to_dec()),
            _ =>
                if self.base == 10 {
                    Ok(self.to_radix_from_dec(base)?)
                } else {
                    Ok(self.to_dec().to_radix_from_dec(base)?)
                },
        }
    }

    /// convert a [`Radix`] into [`Radix`] with base 10
    #[inline]
    fn to_dec(self) -> Self { Self::from(dec!(self)) }

    /// convert a [`Radix`] with base 10 to a [`Radix`] with new base
    fn to_radix_from_dec(mut self, base: u8) -> Result<Self, RadixError> {
        let mut res = String::new();
        while self.number != 0 {
            res.push(RADIX[self.number % (base as usize)]);
            self.number /= base as usize;
        }
        Self::from_radix(res.chars().rev().collect::<String>().parse()?, base)
    }

    /// Translate [`Radix`] to another [`StringRadix`].
    ///
    /// # Panics
    /// Panics if k is less than 2 or k more than 36.
    ///
    /// # Errors
    /// Returns a [`BaseError`] when base isn't correct; [`ParseError`] if there was error with
    /// parse functions.
    ///
    /// [`BaseError`]: RadixError::BaseError
    /// [`ParseError`]: RadixError::ParseError
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::{Radix, StringRadix};
    ///
    /// let n = Radix::from_radix(11010000, 2).unwrap();
    /// let res = n.to_str_radix(16).unwrap();
    /// assert_eq!(res.radix(), ("D0", 16));
    ///
    /// let e = n.to_str_radix(42).unwrap_err();
    /// assert_eq!(e.to_string(), "Expected base in range `2..=36`, found 42");
    /// ```
    pub fn to_str_radix(self, base: u8) -> Result<StringRadix, RadixError> {
        match base {
            0 | 1 | 37.. => Err(RadixError::BaseError(36, base)),
            10 => Ok(StringRadix::from(self.to_dec().number)),
            _ =>
                if self.base == 10 {
                    Ok(self.to_str_radix_from_dec(base)?)
                } else {
                    Ok(self.to_dec().to_str_radix_from_dec(base)?)
                },
        }
    }

    /// convert a [`Radix`] with base 10 number into a [`StringRadix`] number with another base
    fn to_str_radix_from_dec(mut self, base: u8) -> Result<StringRadix, RadixError> {
        let mut res = String::new();
        while self.number != 0 {
            res.push(RADIX[self.number % (base as usize)]);
            self.number /= base as usize;
        }
        StringRadix::from_radix(&res.chars().rev().collect::<String>(), base)
    }

    /// Sum 2 [`Radix`] to new [`StringRadix`].
    ///
    /// # Errors
    /// Same as [`to_str_radix`].
    ///
    /// [`to_str_radix`]: Radix::to_str_radix
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::{Radix, StringRadix};
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// let res = Radix::add_to_str(n1, n2, 16).unwrap();
    /// assert_eq!(res.radix(), ("97", 16));
    /// ```
    #[inline]
    pub fn add_to_str(self, other: Self, base: u8) -> Result<StringRadix, RadixError> {
        (self + other).to_str_radix(base)
    }

    /// Sub 2 [`Radix`] to new [`StringRadix`].
    ///
    /// # Errors
    /// Same as [`to_str_radix`].
    ///
    /// [`to_str_radix`]: Radix::to_str_radix
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::{Radix, StringRadix};
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// let res = Radix::sub_to_str(n2, n1, 16).unwrap();
    /// assert_eq!(res.radix(), ("61", 16));
    /// ```
    #[inline]
    pub fn sub_to_str(self, other: Self, base: u8) -> Result<StringRadix, RadixError> {
        (self - other).to_str_radix(base)
    }

    /// Mul 2 [`Radix`] to new [`StringRadix`].
    ///
    /// # Errors
    /// Same as [`to_str_radix`].
    ///
    /// [`to_str_radix`]: Radix::to_str_radix
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::{Radix, StringRadix};
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// let res = Radix::mul_to_str(n1, n2, 16).unwrap();
    /// assert_eq!(res.radix(), ("D14", 16));
    /// ```
    #[inline]
    pub fn mul_to_str(self, other: Self, base: u8) -> Result<StringRadix, RadixError> {
        (self * other).to_str_radix(base)
    }
}

impl StringRadix {
    /// Creates a new [`StringRadix`].
    ///
    /// # Errors
    /// Returns a [`BaseError`] when base isn't correct.
    ///
    /// [`BaseError`]: RadixError::BaseError
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n = StringRadix::new(2).unwrap();
    /// assert_eq!(n.number(), "0");
    /// assert_eq!(n.base(), 2);
    ///
    /// let e1 = StringRadix::new(1).unwrap_err();
    /// assert_eq!(e1.to_string(), "Expected base in range `2..=36`, found 1");
    ///
    /// let e2 = StringRadix::new(255).unwrap_err();
    /// assert_eq!(e2.to_string(), "Expected base in range `2..=36`, found 255");
    /// ```
    pub fn new(base: u8) -> Result<Self, RadixError> {
        match base {
            0 | 1 | 37.. => Err(RadixError::BaseError(36, base)),
            _ => Ok(Self { number: "0".to_owned(), base }),
        }
    }

    /// Creates a new [`StringRadix`] with given [`str`] number and base.
    ///
    /// # Errors
    /// Returns a [`BaseError`] when base isn't correct or [`NumberError`] when number contains
    /// digit that are more or equal than base.
    ///
    /// [`BaseError`]: RadixError::BaseError
    /// [`NumberError`]: RadixError::NumberError
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n = StringRadix::from_radix("11010000", 2).unwrap();
    /// assert_eq!(n.number(), "11010000");
    /// assert_eq!(n.base(), 2);
    ///
    /// let e = StringRadix::from_radix("129", 9).unwrap_err();
    /// assert_eq!(e.to_string(), "Number contains a digit (9) that is more or equal than base (9)",);
    /// ```
    pub fn from_radix(number: &str, base: u8) -> Result<Self, RadixError> {
        match base {
            0 | 1 | 37.. => Err(RadixError::BaseError(36, base)),
            _ => RADIX
                .iter()
                .skip(base.into())
                .find_map(|&i| number.contains(i).then_some(Err(RadixError::NumberError(i, base))))
                .map_or(Ok(Self { number: number.to_owned(), base }), |err| err),
        }
    }

    /// Returns a number of [`StringRadix`].
    ///
    /// # Example
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let radix = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// assert_eq!(radix.number(), "444");
    /// ```
    #[inline]
    #[must_use]
    pub fn number(&self) -> &str { &self.number }

    /// Returns a base of [`StringRadix`].
    ///
    /// # Example
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let radix = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// assert_eq!(radix.base(), 5);
    /// ```
    #[inline]
    #[must_use]
    pub const fn base(&self) -> u8 { self.base }

    /// Returns a full [`StringRadix`] as tuple `(number, base)`.
    ///
    /// # Example
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let radix = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// assert_eq!(radix.radix(), ("444", 5));
    /// ```
    #[inline]
    #[must_use]
    pub fn radix(&self) -> (&str, u8) { (&self.number, self.base) }

    /// Translate [`StringRadix`] to another [`StringRadix`].
    ///
    /// # Panics
    /// Panics if k is less than 2 or k more than 36.
    ///
    /// # Errors
    /// Returns a [`BaseError`] when base isn't correct; [`ParseError`] if there was error with
    /// parse functions.
    ///
    /// [`BaseError`]: RadixError::BaseError
    /// [`ParseError`]: RadixError::ParseError
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let mut n = StringRadix::from_radix("11010000", 2).unwrap();
    /// let mut res = n.to_radix(16).unwrap();
    /// assert_eq!(res.radix(), ("D0", 16));
    ///
    /// let e = res.to_radix(42).unwrap_err();
    /// assert_eq!(e.to_string(), "Expected base in range `2..=36`, found 42");
    /// ```
    pub fn to_radix(&mut self, base: u8) -> Result<Self, RadixError> {
        match base {
            0 | 1 | 37.. => Err(RadixError::BaseError(36, base)),
            10 => Ok(Self::from(self.to_dec().number)),
            _ =>
                if self.base == 10 {
                    Ok(Self::from_dec(&mut Radix::from(self.number.parse::<usize>()?), base)?)
                } else {
                    Ok(Self::from_dec(&mut self.to_dec(), base)?)
                },
        }
    }

    /// convert [`StringRadix`] to a [`Radix`] number with base 10
    #[inline]
    fn to_dec(&self) -> Radix { Radix::from(dec!(self)) }

    /// convert a [`Radix`] number with base 10 to a new [`StringRadix`] number with another base
    fn from_dec(radix: &mut Radix, base: u8) -> Result<Self, RadixError> {
        let mut res = String::new();
        while radix.number != 0 {
            res.push(RADIX[radix.number % (base as usize)]);
            radix.number /= base as usize;
        }
        Self::from_radix(&res.chars().rev().collect::<String>(), base)
    }

    /// Translate [`StringRadix`] to another [`Radix`].
    ///
    /// # Panics
    /// Panics if k is less than 2 or k more than 36.
    ///
    /// # Errors
    /// Returns a [`BaseError`] when base isn't correct; [`ParseError`] if there was error with
    /// parse functions.
    ///
    /// [`BaseError`]: RadixError::BaseError
    /// [`ParseError`]: RadixError::ParseError
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::{Radix, StringRadix};
    ///
    /// let mut n = StringRadix::from_radix("D14", 16).unwrap();
    /// let res = n.to_int_radix(2).unwrap();
    /// assert_eq!(res.radix(), (110100010100, 2));
    ///
    /// let e = n.to_int_radix(12).unwrap_err();
    /// assert_eq!(e.to_string(), "Expected base in range `2..=10`, found 12");
    /// ```
    pub fn to_int_radix(&mut self, base: u8) -> Result<Radix, RadixError> {
        match base {
            0 | 1 | 11.. => Err(RadixError::BaseError(10, base)),
            10 => Ok(self.to_dec()),
            _ =>
                if self.base == 10 {
                    Ok(Self::from_dec_to_int(
                        &mut Radix::from(self.number.parse::<usize>()?),
                        base,
                    )?)
                } else {
                    Ok(Self::from_dec_to_int(&mut self.to_dec(), base)?)
                },
        }
    }

    /// convert a [`Radix`] number with base 10 to a [`Radix`] with new base
    fn from_dec_to_int(radix: &mut Radix, base: u8) -> Result<Radix, RadixError> {
        let mut res = String::new();
        while radix.number != 0 {
            res.push(RADIX[radix.number % (base as usize)]);
            radix.number /= base as usize;
        }
        Radix::from_radix(res.chars().rev().collect::<String>().parse()?, base)
    }

    /// Sum 2 [`StringRadix`] to new [`Radix`].
    ///
    /// # Errors
    /// Same as [`to_int_radix`].
    ///
    /// [`to_int_radix`]: StringRadix::to_int_radix
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::{Radix, StringRadix};
    ///
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res = StringRadix::add_to_int(n1, n2, 8).unwrap();
    /// assert_eq!(res.radix(), (227, 8));
    /// ```
    #[inline]
    pub fn add_to_int(self, other: Self, base: u8) -> Result<Radix, RadixError> {
        (self + other).to_int_radix(base)
    }

    /// Sub 2 [`StringRadix`] to new [`Radix`].
    ///
    /// # Errors
    /// Same as [`to_int_radix`].
    ///
    /// [`to_int_radix`]: StringRadix::to_int_radix
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::{Radix, StringRadix};
    ///
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res = StringRadix::sub_to_int(n2, n1, 8).unwrap();
    /// assert_eq!(res.radix(), (141, 8));
    /// ```
    #[inline]
    pub fn sub_to_int(self, other: Self, base: u8) -> Result<Radix, RadixError> {
        (self - other).to_int_radix(base)
    }

    /// Mul 2 [`StringRadix`] to new [`Radix`].
    ///
    /// # Errors
    /// Same as [`to_int_radix`].
    ///
    /// [`to_int_radix`]: StringRadix::to_int_radix
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::{Radix, StringRadix};
    ///
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res = StringRadix::mul_to_int(n1, n2, 8).unwrap();
    /// assert_eq!(res.radix(), (6424, 8));
    /// ```
    #[inline]
    pub fn mul_to_int(self, other: Self, base: u8) -> Result<Radix, RadixError> {
        (self * other).to_int_radix(base)
    }
}
