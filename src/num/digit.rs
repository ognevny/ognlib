//! Functions for operations with number digits. It has already been tested, that Iterators are less
//! quick, than `while` loops in these cases.

use std::ops::{AddAssign, DivAssign, MulAssign, Rem};

pub trait Digit {
    fn count(self) -> u8;
    fn has_digit(self, k: u8) -> bool;
    fn rev(self) -> Self;
    fn sum(self) -> Self;
}

impl<N> Digit for N
where
    N: AddAssign + DivAssign + MulAssign + Rem<Output = N> + From<u8> + Copy + Eq,
{
    /// Calculate sum of number digits
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::digit::Digit;
    ///
    /// assert_eq!(123.sum(), 6);
    /// assert_eq!(444.sum(), 12);
    /// ```

    fn sum(mut self) -> Self {
        let mut sum = N::from(0);
        while self != N::from(0) {
            sum += self % N::from(10);
            self /= N::from(10);
        }
        sum
    }

    /// Calculate size of number (how many digits it contains)
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::digit::Digit;
    ///
    /// assert_eq!(123.count(), 3);
    /// assert_eq!(1337228.count(), 7);
    /// ```

    fn count(mut self) -> u8 {
        let mut count = 0;
        while self != N::from(0) {
            self /= N::from(10);
            count += 1;
        }
        count
    }

    /// Reverse number
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::digit::Digit;
    ///
    /// assert_eq!(123.rev(), 321);
    /// assert_eq!(444.rev(), 444);
    /// ```

    fn rev(mut self) -> Self {
        let mut rev = N::from(0);
        while self != N::from(0) {
            rev *= N::from(10);
            rev += self % N::from(10);
            self /= N::from(10);
        }
        rev
    }

    /// Checks, if digit is in number
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::digit::Digit;
    ///
    /// assert_eq!(123.has_digit(2), true);
    /// assert_eq!(444.has_digit(9), false);
    /// ```

    fn has_digit(mut self, k: u8) -> bool {
        while self != N::from(0) {
            if self % N::from(10) == N::from(k) {
                return true;
            }
            self /= N::from(10);
        }
        false
    }
}
