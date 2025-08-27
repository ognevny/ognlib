//! Structs for radix numbers (String nums and int nums). All numbers are unsigned integers.

extern crate alloc;

use {
    super::methods::Num as _,
    alloc::{
        borrow::ToOwned as _,
        string::{String, ToString as _},
    },
    core::{cmp::Ordering, num::ParseIntError, ops, str::FromStr},
    thiserror::Error,
};

/// Reference to a slice of chars from '0' to 'Z' (maximum base is 36).
pub const RADIX: &[char] = &[
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M',
    'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
];

/// A error type for radix functions.
///
/// You can have 2 problems with radix numbers: first, base could be incorrect when it's not in
/// range `2..=10` for [`Radix`] or `2..=36` for [`StringRadix`]; second, number can be incorrect,
/// as number contains digits that are more or equal than base. Also there is can be convertsion
/// error, which is just [`ParseIntError`] from core.
///
/// [`ParseIntError`]: core::num::ParseIntError
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
pub struct Radix<T: Sized + Copy> {
    /// a number of radix number
    number: T,

    /// a base of radix number
    base: u8,
}

impl<T: Sized + Copy + FromStr<Err = ParseIntError>> FromStr for Radix<T> {
    type Err = ParseIntError;

    /// Creates a new [`Radix`] with base 10 and given [`str`] number.
    ///
    /// # Errors
    /// Returns [`ParseIntError`] if number contains invalid digits.
    ///
    /// [`ParseIntError`]: core::num::ParseIntError
    ///
    /// # Examples
    ///
    /// ```
    /// use {core::str::FromStr, ognlib::num::radix::Radix};
    ///
    /// let n = Radix::<usize>::from_str("123").unwrap();
    /// assert_eq!(n.radix(), (123, 10));
    ///
    /// let e = Radix::<usize>::from_str("12A").unwrap_err();
    /// assert_eq!(e.to_string(), "invalid digit found in string");
    /// ```
    #[inline]
    fn from_str(number: &str) -> Result<Self, Self::Err> { Ok(Self { number: number.parse()?, base: 10 }) }
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
    /// [`ParseIntError`]: core::num::ParseIntError
    ///
    /// # Examples
    ///
    /// ```
    /// use {core::str::FromStr, ognlib::num::radix::StringRadix};
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

macro_rules! impl_radix {
    ($($type:ty)*) => {
        $(impl From<$type> for Radix<$type> {
            /// Creates a new [`Radix`] with base 10 and given integer number.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            #[doc = concat!("let radix = Radix::from(123", stringify!($type), ");")]
            #[doc = concat!("assert_eq!(radix.number(), 123", stringify!($type), ");")]
            /// assert_eq!(radix.base(), 10);
            /// ```
            #[inline]
            fn from(number: $type) -> Self {
                Self {
                    number,
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
            #[doc = concat!("let radix = StringRadix::from(123", stringify!($type), ");")]
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
        impl From<Radix<$type>> for $type {
            /// Converts a [`Radix`] into primitive int.
            ///
            /// # Example
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            #[doc = concat!("let radix = Radix::<", stringify!($type), ">::from_radix(124, 5).unwrap();")]
            #[doc = concat!("let num: ", stringify!($type), " = radix.into();")]
            ///
            #[doc = concat!("assert_eq!(num, 39", stringify!($type), ");")]
            /// ```
            #[inline]
            fn from(radix: Radix<$type>) -> Self {
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
        impl From<&Radix<$type>> for $type {
            /// Converts a [`Radix`] into primitive int.
            ///
            /// # Example
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            #[doc = concat!("let radix = Radix::<", stringify!($type), ">::from_radix(124, 5).unwrap();")]
            #[doc = concat!("let num: ", stringify!($type), " = radix.into();")]
            ///
            #[doc = concat!("assert_eq!(num, 39", stringify!($type), ");")]
            /// ```
            #[inline]
            fn from(radix: &Radix<$type>) -> Self {
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
            #[doc = concat!("let num: ", stringify!($type), " = radix.into();")]
            ///
            #[doc = concat!("assert_eq!(num, 124", stringify!($type), ");")]
            /// ```
            #[inline]
            fn from(radix: &StringRadix) -> Self {
                Self::from_str_radix(&radix.number, radix.base.into()).unwrap()
            }
        }

        impl PartialOrd for Radix<$type> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                Some(self.cmp(other))
            }

            fn gt(&self, other: &Self) -> bool {
                Into::<$type>::into(self) > Into::<$type>::into(other)
            }

            fn lt(&self, other: &Self) -> bool {
                Into::<$type>::into(self) < Into::<$type>::into(other)
            }

            fn le(&self, other: &Self) -> bool {
                Into::<$type>::into(self) <= Into::<$type>::into(other)
            }

            fn ge(&self, other: &Self) -> bool {
                Into::<$type>::into(self) >= Into::<$type>::into(other)
            }
        }

        impl Ord for Radix<$type> {
            fn cmp(&self, other: &Self) -> Ordering {
                Into::<$type>::into(self).cmp(&Into::<$type>::into(other))
            }

            fn max(self, other: Self) -> Self {
                if self > other {
                    self
                } else {
                    other
                }
            }

            fn min(self, other: Self) -> Self {
                if self < other {
                    self
                } else {
                    other
                }
            }

            fn clamp(self, min: Self, max: Self) -> Self {
                assert!(max >= min);
                if self < min {
                    min
                } else if self > max {
                    max
                } else {
                    self
                }
            }
        }

        impl ops::Add for Radix<$type> {
            type Output = Self;

            /// Performs a `+` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            /// let res = (n1 + n2).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (227, 8));
            /// ```
            fn add(self, rhs: Self) -> Self::Output {
                Self::from(Into::<$type>::into(self) + Into::<$type>::into(rhs))
                    .to_radix(self.base)
                    .unwrap()
            }
        }
        impl ops::Add<$type> for Radix<$type> {
            type Output = Self;

            /// Performs a `+` operation ([`usize`] as `rhs`).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let n = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let res = (n + 124).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (227, 8));
            /// ```
            fn add(self, rhs: $type) -> Self::Output {
                Self::from(Into::<$type>::into(self) + rhs)
                    .to_radix(self.base)
                    .unwrap()
            }
        }
        impl ops::AddAssign for Radix<$type> {
            /// Performs a `+=` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let mut n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            /// n1 += n2;
            ///
            /// n1 = n1.to_radix(8).unwrap();
            /// assert_eq!(n1.radix(), (227, 8));
            /// ```
            fn add_assign(&mut self, rhs: Self) {
                *self = *self + rhs
            }
        }
        impl ops::AddAssign<$type> for Radix<$type> {
            /// Performs a `+=` operation ([`usize`] is rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let mut n = Radix::<usize>::from_radix(123, 4).unwrap();
            /// n += 124;
            ///
            /// n = n.to_radix(8).unwrap();
            /// assert_eq!(n.radix(), (227, 8));
            /// ```
            fn add_assign(&mut self, rhs: $type) {
                *self = *self + Self::from(rhs)
            }
        }
        impl ops::Sub for Radix<$type> {
            type Output = Self;

            /// Performs a `-` operation. Result of the operation is an absolute value. Base of the
            /// resulting number is the base of the greater number.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            /// let res = (n1 - n2).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (141, 8));
            /// ```
            fn sub(self, rhs: Self) -> Self::Output {
                if self > rhs {
                    Self::from(Into::<$type>::into(self) - Into::<$type>::into(rhs))
                        .to_radix(self.base)
                        .unwrap()
                } else {
                    Self::from(Into::<$type>::into(rhs) - Into::<$type>::into(self))
                        .to_radix(rhs.base)
                        .unwrap()
                }
            }
        }
        impl ops::Sub<$type> for Radix<$type> {
            type Output = Self;

            /// Performs a `-` operation ([`usize`] is rhs). Result of operation is an absolute
            /// value. Base of resulting number is the base of greater number.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let n = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let res = (n - 124).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (141, 8));
            /// ```
            fn sub(self, rhs: $type) -> Self::Output {
                if self > Self::from(rhs) {
                    Self::from(Into::<$type>::into(self) - rhs)
                        .to_radix(self.base)
                        .unwrap()
                } else {
                    Self::from(rhs - Into::<$type>::into(self))
                        .to_radix(10)
                        .unwrap()
                }
            }
        }
        impl ops::SubAssign for Radix<$type> {
            /// Performs a `-=` operation. The same rules as for common sub are applied.
            ///
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let mut n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            /// n1 -= n2;
            ///
            /// n1 = n1.to_radix(8).unwrap();
            /// assert_eq!(n1.radix(), (141, 8));
            /// ```
            fn sub_assign(&mut self, rhs: Self) {
                *self = *self - rhs;
            }
        }
        impl ops::SubAssign<$type> for Radix<$type> {
            /// Performs a `-=` operation ([`usize`] as rhs).
            ///
            /// The same rules as for common sub are applied.
            ///
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let mut n  = Radix::<usize>::from_radix(123, 4).unwrap();
            /// n -= 124;
            ///
            /// n = n.to_radix(8).unwrap();
            ///
            /// assert_eq!(n.radix(), (141, 8));
            /// ```
            fn sub_assign(&mut self, rhs: $type) {
                *self = *self - rhs;
            }
        }
        impl ops::Mul for Radix<$type> {
            type Output = Self;

            /// Performs a `*` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            ///
            /// let res = (n1 * n2).to_radix(8).unwrap();
            /// assert_eq!(res.radix(), (6424, 8));
            /// ```
            fn mul(self, rhs: Self) -> Self::Output {
                Self::from(Into::<$type>::into(self) * Into::<$type>::into(rhs))
                    .to_radix(self.base)
                    .unwrap()
            }
        }
        impl ops::Mul<$type> for Radix<$type> {
            type Output = Self;

            /// Performs a `*` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let n = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let res = (n * 124).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (6424, 8));
            /// ```
            fn mul(self, rhs: $type) -> Self::Output {
                Self::from(Into::<$type>::into(self) * rhs)
                    .to_radix(self.base)
                    .unwrap()
            }
        }
        impl ops::MulAssign for Radix<$type> {
            /// Performs a `*=` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let mut n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            /// n1 *= n2;
            ///
            /// n1 = n1.to_radix(8).unwrap();
            /// assert_eq!(n1.radix(), (6424, 8));
            /// ```
            fn mul_assign(&mut self, rhs: Self) {
                *self = *self * rhs;
            }
        }
        impl ops::MulAssign<$type> for Radix<$type> {
            /// Performs a `*=` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let mut n = Radix::<usize>::from_radix(123, 4).unwrap();
            /// n *= 124;
            ///
            /// n = n.to_radix(8).unwrap();
            /// assert_eq!(n.radix(), (6424, 8));
            /// ```
            fn mul_assign(&mut self, rhs: $type) {
                *self = *self * rhs;
            }
        }
        impl ops::Div for Radix<$type> {
            type Output = Self;

            /// Performs a `/` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            ///
            /// let res = (n2 / n1).to_radix(8).unwrap();
            /// assert_eq!(res.radix(), (4, 8));
            /// ```
            fn div(self, rhs: Self) -> Self::Output {
                Self::from(Into::<$type>::into(self) / Into::<$type>::into(rhs))
                    .to_radix(self.base)
                    .unwrap()
            }
        }
        impl ops::Div<$type> for Radix<$type> {
            type Output = Self;

            /// Performs a `/` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let n = Radix::<usize>::from_radix(444, 5).unwrap();
            /// let res = (n / 27).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (4, 8));
            /// ```
            fn div(self, rhs: $type) -> Self::Output {
                Self::from(Into::<$type>::into(self) / rhs)
                    .to_radix(self.base)
                    .unwrap()
            }
        }
        impl ops::DivAssign for Radix<$type> {
            /// Performs a `/=` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let mut n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            /// n2 /= n1;
            ///
            /// n2 = n2.to_radix(8).unwrap();
            ///
            /// assert_eq!(n2.radix(), (4, 8));
            /// ```
            fn div_assign(&mut self, rhs: Self) {
                *self = *self / rhs;
            }
        }
        impl ops::DivAssign<$type> for Radix<$type> {
            /// Performs a `/=` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let mut n = Radix::<usize>::from_radix(444, 5).unwrap();
            /// n /= 27;
            ///
            /// n = n.to_radix(8).unwrap();
            /// assert_eq!(n.radix(), (4, 8));
            /// ```
            fn div_assign(&mut self, rhs: $type) {
                *self = *self / rhs;
            }
        }
        impl ops::Rem for Radix<$type> {
            type Output = Self;

            /// Performs a `%` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::{Radix, StringRadix};
            ///
            /// let n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            ///
            /// let res = (n2 % n1).to_radix(8).unwrap();
            /// assert_eq!(res.radix(), (20, 8));
            /// ```
            fn rem(self, rhs: Self) -> Self::Output {
                Self::from(Into::<$type>::into(self) % Into::<$type>::into(rhs))
                    .to_radix(self.base)
                    .unwrap()
            }
        }
        impl ops::Rem<$type> for Radix<$type> {
            type Output = Self;

            /// Performs a `%` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let n = Radix::<usize>::from_radix(444, 5).unwrap();
            /// let res = (n % 27).to_radix(8).unwrap();
            ///
            /// assert_eq!(res.radix(), (20, 8));
            /// ```
            fn rem(self, rhs: $type) -> Self::Output {
                Self::from(Into::<$type>::into(self) % rhs)
                    .to_radix(self.base)
                    .unwrap()
            }
        }
        impl ops::RemAssign for Radix<$type> {
            /// Performs a `%=` operation.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let mut n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            /// n2 %= n1;
            ///
            /// n2 = n2.to_radix(8).unwrap();
            /// assert_eq!(n2.radix(), (20, 8));
            /// ```
            fn rem_assign(&mut self, rhs: Self) {
                *self = *self % rhs;
            }
        }
        impl ops::RemAssign<$type> for Radix<$type> {
            /// Performs a `%=` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let mut n = Radix::<usize>::from_radix(444, 5).unwrap();
            /// n %= 27usize;
            ///
            /// assert_eq!(n.radix(), (31, 5));
            /// ```
            fn rem_assign(&mut self, rhs: $type) {
                *self = *self % rhs;
            }
        }

        impl ops::Add<$type> for StringRadix {
            type Output = Self;

            /// Performs a `+` operation ([`usize`] as `rhs`).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let n_str = StringRadix::from_radix("123", 4).unwrap();
            /// let res_str = (n_str + 124u32).to_radix(8).unwrap();
            ///
            /// assert_eq!(res_str.radix(), ("227", 8));
            /// ```
            fn add(self, rhs: $type) -> Self::Output {
                Self::from(Into::<$type>::into(&self) + rhs)
                    .to_radix(self.base)
                    .unwrap()
            }
        }
        impl ops::AddAssign<$type> for StringRadix {
            /// Performs a `+=` operation ([`usize`] is rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let mut n_str = StringRadix::from_radix("123", 4).unwrap();
            /// n_str += 124u32;
            ///
            /// n_str = n_str.to_radix(8).unwrap();
            /// assert_eq!(n_str.radix(), ("227", 8));
            /// ```
            fn add_assign(&mut self, rhs: $type) {
                *self = self.clone() + Self::from(rhs)
            }
        }
        impl ops::Sub<$type> for StringRadix {
            type Output = Self;

            /// Performs a `-` operation ([`usize`] is rhs). Result of operation is an absolute
            /// value. Base of resulting number is the base of greater number.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let n_str = StringRadix::from_radix("123", 4).unwrap();
            /// let res_str = (n_str - 124u32).to_radix(8).unwrap();
            ///
            /// assert_eq!(res_str.radix(), ("141", 8));
            /// ```
            fn sub(self, rhs: $type) -> Self::Output {
                if self > Self::from(rhs) {
                    Self::from(Into::<$type>::into(&self) - rhs)
                        .to_radix(self.base)
                        .unwrap()
                } else {
                    Self::from(rhs - Into::<$type>::into(self))
                        .to_radix(10)
                        .unwrap()
                }
            }
        }
        impl ops::SubAssign<$type> for StringRadix {
            /// Performs a `-=` operation ([`usize`] as rhs).
            ///
            /// The same rules as for common sub are applied.
            ///
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let mut n_str = StringRadix::from_radix("123", 4).unwrap();
            /// n_str -= 124u32;
            ///
            /// n_str = n_str.to_radix(8).unwrap();
            /// assert_eq!(n_str.radix(), ("141", 8));
            /// ```
            fn sub_assign(&mut self, rhs: $type) {
                *self = self.clone() - rhs;
            }
        }
        impl ops::Mul<$type> for StringRadix {
            type Output = Self;

            /// Performs a `*` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let n_str = StringRadix::from_radix("123", 4).unwrap();
            /// let res_str = (n_str * 124u32).to_radix(8).unwrap();
            ///
            /// assert_eq!(res_str.radix(), ("6424", 8));
            /// ```
            fn mul(self, rhs: $type) -> Self::Output {
                Self::from(Into::<$type>::into(&self) * rhs)
                    .to_radix(self.base)
                    .unwrap()
            }
        }
        impl ops::MulAssign<$type> for StringRadix {
            /// Performs a `*=` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let mut n_str = StringRadix::from_radix("123", 4).unwrap();
            /// n_str *= 124u32;
            ///
            /// n_str = n_str.to_radix(8).unwrap();
            /// assert_eq!(n_str.radix(), ("6424", 8));
            /// ```
            fn mul_assign(&mut self, rhs: $type) {
                *self = self.clone() * rhs;
            }
        }
        impl ops::Div<$type> for StringRadix {
            type Output = Self;

            /// Performs a `/` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let n_str = StringRadix::from_radix("444", 5).unwrap();
            /// let res_str = (n_str / 27u32).to_radix(8).unwrap();
            ///
            /// assert_eq!(res_str.radix(), ("4", 8));
            /// ```
            fn div(self, rhs: $type) -> Self::Output {
                Self::from(Into::<$type>::into(&self) / rhs)
                    .to_radix(self.base)
                    .unwrap()
            }
        }
        impl ops::DivAssign<$type> for StringRadix {
            /// Performs a `/=` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let mut n_str = StringRadix::from_radix("444", 5).unwrap();
            /// n_str /= 27u32;
            ///
            /// n_str = n_str.to_radix(8).unwrap();
            /// assert_eq!(n_str.radix(), ("4", 8));
            /// ```
            fn div_assign(&mut self, rhs: $type) {
                *self = self.clone() / rhs;
            }
        }
        impl ops::Rem<$type> for StringRadix {
            type Output = Self;

            /// Performs a `%` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let n_str = StringRadix::from_radix("444", 5).unwrap();
            /// let res_str = (n_str % 27u32).to_radix(8).unwrap();
            ///
            /// assert_eq!(res_str.radix(), ("20", 8));
            /// ```
            fn rem(self, rhs: $type) -> Self::Output {
                Self::from(Into::<$type>::into(&self) % rhs)
                    .to_radix(self.base)
                    .unwrap()
            }
        }
        impl ops::RemAssign<$type> for StringRadix {
            /// Performs a `%=` operation ([`usize`] as rhs).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::radix::StringRadix;
            ///
            /// let mut n_str = StringRadix::from_radix("444", 5).unwrap();
            /// n_str %= 27u32;
            ///
            /// n_str = n_str.to_radix(8).unwrap();
            /// assert_eq!(n_str.radix(), ("20", 8));
            /// ```
            fn rem_assign(&mut self, rhs: $type) {
                *self = self.clone() % rhs;
            }
        }

        impl Radix<$type> {
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
            /// let n = Radix::<usize>::new(2).unwrap();
            /// assert_eq!(n.number(), 0);
            /// assert_eq!(n.base(), 2);
            ///
            /// let e1 = Radix::<usize>::new(1).unwrap_err();
            /// assert_eq!(e1.to_string(), "Expected base in range `2..=10`, found 1");
            ///
            /// let e2 = Radix::<usize>::new(33).unwrap_err();
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
            /// # Panics
            /// Panics if a char from [`RADIX`] is somehow not parsed
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
            /// let n = Radix::<usize>::from_radix(11010000usize, 2).unwrap();
            /// assert_eq!(n.number(), 11010000);
            /// assert_eq!(n.base(), 2);
            ///
            /// let e = Radix::<usize>::from_radix(444, 3).unwrap_err();
            /// assert_eq!(e.to_string(), "Number contains a digit (4) that is more or equal than base (3)",);
            /// ```
            pub fn from_radix(number: $type, base: u8) -> Result<Self, RadixError> {
                match base {
                    0 | 1 | 11.. => Err(RadixError::BaseError(10, base)),
                    _ => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
                        .into_iter()
                        .skip(base.into())
                        .find_map(|i| {
                            number
                                .has_digit(i)
                                .then_some(Err(RadixError::NumberError(RADIX[i as usize], base)))
                        })
                        .map_or(Ok(Self { number, base }), |err| err),
                }
            }

            /// Returns a number of [`Radix`].
            ///
            /// # Example
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let radix = Radix::<usize>::from_radix(444, 5).unwrap();
            ///
            /// assert_eq!(radix.number(), 444);
            /// ```
            #[inline]
            #[must_use]
            pub const fn number(&self) -> $type { self.number }

            /// Returns a base of [`Radix`].
            ///
            /// # Example
            ///
            /// ```
            /// use ognlib::num::radix::Radix;
            ///
            /// let radix = Radix::<usize>::from_radix(444, 5).unwrap();
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
            /// let radix = Radix::<usize>::from_radix(444, 5).unwrap();
            ///
            /// assert_eq!(radix.radix(), (444, 5));
            /// ```
            #[inline]
            #[must_use]
            pub const fn radix(&self) -> ($type, u8) { (self.number, self.base) }

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
            /// let n1 = Radix::<usize>::from(123);
            /// let new1 = n1.to_radix(8).unwrap();
            ///
            /// let n2 = Radix::<usize>::from_radix(173, 8).unwrap();
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
            fn to_dec(self) -> Self { Self::from(Into::<$type>::into(self)) }

            /// convert a [`Radix`] with base 10 to a [`Radix`] with new base
            fn to_radix_from_dec(mut self, base: u8) -> Result<Self, RadixError> {
                let mut res = String::new();
                while self.number != 0 {
                    res.push(RADIX[self.number as usize % Into::<usize>::into(base)]);
                    self.number /= Into::<$type>::into(base);
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
            /// let n = Radix::<usize>::from_radix(11010000usize, 2).unwrap();
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
                    res.push(RADIX[self.number as usize % Into::<usize>::into(base)]);
                    self.number /= Into::<$type>::into(base);
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
            /// let n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            ///
            /// let res = Radix::<usize>::add_to_str(n1, n2, 16).unwrap();
            /// assert_eq!(res.radix(), ("97", 16));
            /// ```
            #[inline]
            pub fn add_to_str(self, rhs: Self, base: u8) -> Result<StringRadix, RadixError> {
                (self + rhs).to_str_radix(base)
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
            /// let n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            ///
            /// let res = Radix::<usize>::sub_to_str(n2, n1, 16).unwrap();
            /// assert_eq!(res.radix(), ("61", 16));
            /// ```
            #[inline]
            pub fn sub_to_str(self, rhs: Self, base: u8) -> Result<StringRadix, RadixError> {
                (self - rhs).to_str_radix(base)
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
            /// let n1 = Radix::<usize>::from_radix(123, 4).unwrap();
            /// let n2 = Radix::<usize>::from_radix(444, 5).unwrap();
            ///
            /// let res = Radix::<usize>::mul_to_str(n1, n2, 16).unwrap();
            /// assert_eq!(res.radix(), ("D14", 16));
            /// ```
            #[inline]
            pub fn mul_to_str(self, rhs: Self, base: u8) -> Result<StringRadix, RadixError> {
                (self * rhs).to_str_radix(base)
            }
        })*
    };
}

impl_radix!(u8 u16 u32 u64 usize);

impl PartialOrd for StringRadix {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) }

    fn gt(&self, other: &Self) -> bool { Into::<usize>::into(self) > Into::<usize>::into(other) }

    fn lt(&self, other: &Self) -> bool { Into::<usize>::into(self) < Into::<usize>::into(other) }

    fn le(&self, other: &Self) -> bool { Into::<usize>::into(self) <= Into::<usize>::into(other) }

    fn ge(&self, other: &Self) -> bool { Into::<usize>::into(self) >= Into::<usize>::into(other) }
}

impl Ord for StringRadix {
    fn cmp(&self, other: &Self) -> Ordering { Into::<usize>::into(self).cmp(&Into::<usize>::into(other)) }

    fn max(self, other: Self) -> Self { if self > other { self } else { other } }

    fn min(self, other: Self) -> Self { if self < other { self } else { other } }

    fn clamp(self, min: Self, max: Self) -> Self {
        assert!(max >= min, "min can't be more than max");
        if self < min {
            min
        } else if self > max {
            max
        } else {
            self
        }
    }
}

impl ops::Add for StringRadix {
    type Output = Self;

    /// Performs a `+` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res_str = (n_str1 + n_str2).to_radix(8).unwrap();
    /// assert_eq!(res_str.radix(), ("227", 8));
    /// ```
    fn add(self, rhs: Self) -> Self::Output {
        Self::from(Into::<usize>::into(&self) + Into::<usize>::into(&rhs)).to_radix(self.base).unwrap()
    }
}
impl ops::AddAssign for StringRadix {
    /// Performs a `+=` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let mut n_str1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
    /// n_str1 += n_str2;
    ///
    /// n_str1 = n_str1.to_radix(8).unwrap();
    /// assert_eq!(n_str1.radix(), ("227", 8));
    /// ```
    fn add_assign(&mut self, rhs: Self) { *self = self.clone() + rhs }
}
impl ops::Sub for StringRadix {
    type Output = Self;

    /// Performs a `-` operation. Result of the operation is an absolute value. Base of the
    /// resulting number is the base of the greater number.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res_str = (n_str1 - n_str2).to_radix(8).unwrap();
    /// assert_eq!(res_str.radix(), ("141", 8));
    /// ```
    fn sub(self, rhs: Self) -> Self::Output {
        if self > rhs {
            Self::from(Into::<usize>::into(&self) - Into::<usize>::into(&rhs)).to_radix(self.base).unwrap()
        } else {
            Self::from(Into::<usize>::into(&rhs) - Into::<usize>::into(&self)).to_radix(rhs.base).unwrap()
        }
    }
}
impl ops::SubAssign for StringRadix {
    /// Performs a `-=` operation. The same rules as for common sub are applied.
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let mut n_str1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
    /// n_str1 -= n_str2;
    ///
    /// n_str1 = n_str1.to_radix(8).unwrap();
    /// assert_eq!(n_str1.radix(), ("141", 8));
    /// ```
    fn sub_assign(&mut self, rhs: Self) { *self = self.clone() - rhs; }
}
impl ops::Mul for StringRadix {
    type Output = Self;

    /// Performs a `*` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res_str = (n_str1 * n_str2).to_radix(8).unwrap();
    /// assert_eq!(res_str.radix(), ("6424", 8));
    /// ```
    fn mul(self, rhs: Self) -> Self::Output {
        Self::from(Into::<usize>::into(&self) * Into::<usize>::into(&rhs)).to_radix(self.base).unwrap()
    }
}
impl ops::MulAssign for StringRadix {
    /// Performs a `*=` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let mut n_str1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
    /// n_str1 *= n_str2;
    ///
    /// n_str1 = n_str1.to_radix(8).unwrap();
    /// assert_eq!(n_str1.radix(), ("6424", 8));
    /// ```
    fn mul_assign(&mut self, rhs: Self) { *self = self.clone() * rhs; }
}
impl ops::Div for StringRadix {
    type Output = Self;

    /// Performs a `/` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res_str = (n_str2 / n_str1).to_radix(8).unwrap();
    /// assert_eq!(res_str.radix(), ("4", 8));
    /// ```
    fn div(self, rhs: Self) -> Self::Output {
        Self::from(Into::<usize>::into(&self) / Into::<usize>::into(&rhs)).to_radix(self.base).unwrap()
    }
}
impl ops::DivAssign for StringRadix {
    /// Performs a `/=` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
    /// let mut n_str2 = StringRadix::from_radix("444", 5).unwrap();
    /// n_str2 /= n_str1;
    ///
    /// n_str2 = n_str2.to_radix(8).unwrap();
    /// assert_eq!(n_str2.radix(), ("4", 8));
    /// ```
    fn div_assign(&mut self, rhs: Self) { *self = self.clone() / rhs; }
}
impl ops::Rem for StringRadix {
    type Output = Self;

    /// Performs a `%` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n_str2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res_str = (n_str2 % n_str1).to_radix(8).unwrap();
    /// assert_eq!(res_str.radix(), ("20", 8));
    /// ```
    fn rem(self, rhs: Self) -> Self::Output {
        Self::from(Into::<usize>::into(&self) % Into::<usize>::into(&rhs)).to_radix(self.base).unwrap()
    }
}
impl ops::RemAssign for StringRadix {
    /// Performs a `%=` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n_str1 = StringRadix::from_radix("123", 4).unwrap();
    /// let mut n_str2 = StringRadix::from_radix("444", 5).unwrap();
    /// n_str2 %= n_str1;
    ///
    /// n_str2 = n_str2.to_radix(8).unwrap();
    ///
    /// assert_eq!(n_str2.radix(), ("20", 8));
    /// ```
    fn rem_assign(&mut self, rhs: Self) { *self = self.clone() % rhs; }
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
                .map_or_else(|| Ok(Self { number: number.to_owned(), base }), |err| err),
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
    fn to_dec(&self) -> Radix<usize> { Radix::from(Into::<usize>::into(self)) }

    /// convert a [`Radix`] number with base 10 to a new [`StringRadix`] number with another base
    fn from_dec(radix: &mut Radix<usize>, base: u8) -> Result<Self, RadixError> {
        let mut res = String::new();
        while radix.number != 0 {
            res.push(RADIX[radix.number % Into::<usize>::into(base)]);
            radix.number /= Into::<usize>::into(base);
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
    pub fn to_int_radix(&mut self, base: u8) -> Result<Radix<usize>, RadixError> {
        match base {
            0 | 1 | 11.. => Err(RadixError::BaseError(10, base)),
            10 => Ok(self.to_dec()),
            _ =>
                if self.base == 10 {
                    Ok(Self::from_dec_to_int(&mut Radix::from(self.number.parse::<usize>()?), base)?)
                } else {
                    Ok(Self::from_dec_to_int(&mut self.to_dec(), base)?)
                },
        }
    }

    /// convert a [`Radix`] number with base 10 to a [`Radix`] with new base
    fn from_dec_to_int(radix: &mut Radix<usize>, base: u8) -> Result<Radix<usize>, RadixError> {
        let mut res = String::new();
        while radix.number != 0 {
            res.push(RADIX[radix.number % Into::<usize>::into(base)]);
            radix.number /= Into::<usize>::into(base);
        }
        Radix::<usize>::from_radix(res.chars().rev().collect::<String>().parse()?, base)
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
    pub fn add_to_int(self, rhs: Self, base: u8) -> Result<Radix<usize>, RadixError> { (self + rhs).to_int_radix(base) }

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
    pub fn sub_to_int(self, rhs: Self, base: u8) -> Result<Radix<usize>, RadixError> { (self - rhs).to_int_radix(base) }

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
    pub fn mul_to_int(self, rhs: Self, base: u8) -> Result<Radix<usize>, RadixError> { (self * rhs).to_int_radix(base) }
}
