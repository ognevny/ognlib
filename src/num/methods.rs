//! Functions for operations with number digits. It has already been tested, that Iterators are less
//! quick, than `while` loops in these cases.

use num_bigint::BigUint;
#[cfg(feature = "std")] use rayon::prelude::*;

pub trait Num {
    /// Represent number as bool like in C.
    fn as_bool(&self) -> bool;

    /// Calculate size of number (how many digits it contains).
    fn count(self) -> u32;

    /// Checks, if digit is in number.
    fn has_digit(self, k: Self) -> bool;

    /// Reverse number.
    #[must_use]
    fn rev(self) -> Self;

    /// Calculate sum of number digits.
    #[must_use]
    fn sum(self) -> Self;

    /// Calculates factorial of number (result is [`num_bigint::BigUint`]).
    fn factorial(self) -> BigUint;
}

/// impl Num trait's methods
macro_rules! impl_num {
    ($($type:ty)*) => {
        $(impl Num for $type {
            /// Represent number as bool like in C.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::methods::Num;
            ///
            /// assert!(123.as_bool());
            /// assert!(!0.as_bool());
            /// ```
            #[inline]
            fn as_bool(&self) -> bool {
                *self != 0
            }

            /// Calculate sum of number digits.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::methods::Num;
            ///
            /// assert_eq!(123.sum(), 6);
            /// assert_eq!(444.sum(), 12);
            /// ```
            #[must_use]
            fn sum(self) -> Self {
                let mut num = self;
                let mut sum = 0;
                while num.as_bool() {
                    sum += num % 10;
                    num /= 10;
                }
                sum
            }

            /// Calculate size of number (how many digits it contains).
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::methods::Num;
            ///
            /// assert_eq!(123.count(), 3);
            /// assert_eq!(1337228.count(), 7);
            /// ```
            #[inline]
            fn count(self) -> u32 {
                (self.ilog10() + 1)
            }

            /// Reverse number.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::methods::Num;
            ///
            /// assert_eq!(123.rev(), 321);
            /// assert_eq!(444.rev(), 444);
            /// ```
            #[must_use]
            fn rev(self) -> Self {
                let mut num = self;
                let mut rev = 0;
                while num.as_bool() {
                    rev *= 10;
                    rev += num % 10;
                    num /= 10;
                }
                rev
            }

            /// Checks, if digit is in number.
            /// # Examples
            ///
            /// ```
            /// use ognlib::num::methods::Num;
            ///
            /// assert_eq!(123.has_digit(2), true);
            /// assert_eq!(444.has_digit(9), false);
            /// ```
            fn has_digit(self, digit: Self) -> bool {
                let mut num = self;
                while num.as_bool() {
                    if num % 10 == digit {
                        return true;
                    }
                    num /= 10;
                }
                false
            }

            /// Factorial of number (result is [`num_bigint::BigUint`]).
            /// # Examples
            ///
            /// ```
            /// use {ognlib::num::methods::Num, num_bigint::BigUint};
            ///
            /// let (n1, n2) = (3.factorial(), 5.factorial());
            /// assert_eq!(n1, BigUint::from(6u8));
            /// assert_eq!(n2, BigUint::from(120u8))
            /// ```
            fn factorial(self) -> BigUint {
                let num = self as usize;
                match num {
                    0 | 1 => BigUint::from(1u8),
                    _ => {
                        cfg_if::cfg_if! {
                            if #[cfg(feature = "std")] {
                                (2..=num).into_par_iter().map(BigUint::from).product()
                            } else {
                                (2..=num).map(BigUint::from).product()
                            }
                        }
                    },
                }
            }
        })*
    }
}

impl_num!(i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize);
