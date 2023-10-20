//! Functions for operations with number digits. It has already been tested, that Iterators are less
//! quick, than `while` loops in these cases.

use num_bigint::BigInt;

pub trait Num {
    /// Represent number as bool like in C.
    fn as_bool(&self) -> bool;

    /// Calculate size of number (how many digits it contains).
    fn count(self) -> u8;

    /// Checks, if digit is in number.
    fn has_digit(self, k: u8) -> bool;

    /// Reverse number.
    fn rev(self) -> Self;

    /// Calculate sum of number digits.
    fn sum(self) -> Self;

    /// Calculates factorial of number (result is BigInt)
    fn factorial(self) -> BigInt;
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

            fn sum(mut self) -> Self {
                let mut sum = 0;
                while self.as_bool() {
                    sum += self % 10;
                    self /= 10;
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

            fn count(mut self) -> u8 {
                let mut count = 0;
                while self.as_bool() {
                    self /= 10;
                    count += 1;
                }
                count
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

            fn rev(mut self) -> Self {
                let mut rev = 0;
                while self.as_bool() {
                    rev *= 10;
                    rev += self % 10;
                    self /= 10;
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

            fn has_digit(mut self, k: u8) -> bool {
                while self.as_bool() {
                    if self % 10 == k.try_into().unwrap() {
                        return true;
                    }
                    self /= 10;
                }
                false
            }

            /// Factorial of number
            /// # Examples
            ///
            /// ```
            /// use num_bigint::BigInt;
            /// use ognlib::num::methods::Num;
            ///
            /// let (n1, n2) = (3.factorial(), 5.factorial());
            /// assert_eq!(n1, BigInt::from(6));
            /// assert_eq!(n2, BigInt::from(120))
            /// ```

            fn factorial(self) -> BigInt {
                if self <= 0 {
                    return BigInt::from(1);
                }
                let mut res = BigInt::from(1);
                for i in (1..=self) {
                    res *= BigInt::from(i);
                }
                res
            }
        })*
    }
}

impl_num!(i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize);
