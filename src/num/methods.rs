//! Functions for operations with number digits. It has already been tested, that Iterators are less
//! quick, than `while` loops in these cases.

#[cfg(feature = "num-bigint")]
use {num_bigint::BigInt, rayon::prelude::*};

pub trait Num {
    /// Represent number as bool like in C.
    fn as_bool(&self) -> bool;

    /// Calculate size of number (how many digits it contains).
    fn count(self) -> u8;

    /// Checks, if digit is in number.
    fn has_digit(self, k: Self) -> bool;

    /// Reverse number.
    fn rev(self) -> Self;

    /// Calculate sum of number digits.
    fn sum(self) -> Self;
    #[cfg(feature = "num-bigint")]
    /// Calculates factorial of number (result is [`num_bigint::BigInt`]).
    fn factorial(self) -> num_bigint::BigInt;
}

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

            fn sum(self) -> Self {
                let mut n = self;
                let mut sum = 0;
                while n.as_bool() {
                    sum += n % 10;
                    n /= 10;
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
            fn count(self) -> u8 {
                (self.ilog10() + 1) as u8
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

            fn rev(self) -> Self {
                let mut n = self;
                let mut rev = 0;
                while n.as_bool() {
                    rev *= 10;
                    rev += n % 10;
                    n /= 10;
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

            fn has_digit(self, k: Self) -> bool {
                let mut n = self;
                while n.as_bool() {
                    if n % 10 == k {
                        return true;
                    }
                    n /= 10;
                }
                false
            }

            /// Factorial of number (result is [`num_bigint::BigInt`]).
            /// # Examples
            ///
            /// ```
            /// use {ognlib::num::methods::Num, num_bigint::BigInt};
            ///
            /// let (n1, n2) = (3.factorial(), 5.factorial());
            /// assert_eq!(n1, BigInt::from(6));
            /// assert_eq!(n2, BigInt::from(120))
            /// ```
            #[cfg(feature = "num-bigint")]
            fn factorial(self) -> BigInt {
                match self {
                    0 | 1 => BigInt::from(1),
                    _ => (2..=self).into_par_iter().map(BigInt::from).product(),
                }
            }
        })*
    }
}

impl_num!(i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize);
