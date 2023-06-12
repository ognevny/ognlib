//! Structs and impls for radix numbers (String nums and int nums). All numbers are unsigned ints.

// TODO: write tests

use std::{cmp::Ordering, error::Error, fmt, ops};

/// Reference to slice of chars from '0' to 'Z' (maximum base is 36).
pub const RADIX: &[char] = &[
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I',
    'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
];

/// You can have 2 problems with radix numbers: first, base could be incorrect when it's not in
/// range `2..=10` for [`Radix`] or `2..=36` for [`StringRadix`]; second, number can be incorrect,
/// this could be caused by fact that number contains digits that are more or equal than base. So
/// this enum is about these 2 problems. But also there is ParseError which is just
/// [`ParseIntError`] from std.
/// 
/// [`ParseIntError`]: std::num::ParseIntError
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RadixError<'a> {
    BaseError(&'a str),
    NumberError(&'a str),
    ParseError(std::num::ParseIntError),
}

impl<'a> fmt::Display for RadixError<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            RadixError::BaseError(e) => write!(f, "Base error: {e}"),
            RadixError::NumberError(e) => write!(f, "Number error: {e}"),
            RadixError::ParseError(e) => write!(f, "Conversion error: {e}"),
        }
    }
}

impl<'a> Error for RadixError<'a> {}

/// Radix number, that is usually written as *number*<sub>*base*</sub> (444<sub>8</sub> for
/// example). So fields are named in that way. Base can be only in range `2..=10`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Radix {
    pub number: usize,
    pub base: u8,
}

impl PartialOrd for Radix {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        usize::from_str_radix(&self.number.to_string(), self.base.into())
            .unwrap()
            .partial_cmp(
                &usize::from_str_radix(&other.number.to_string(), other.base.into()).unwrap(),
            )
    }
}

impl Ord for Radix {
    fn cmp(&self, other: &Self) -> Ordering {
        usize::from_str_radix(&self.number.to_string(), self.base.into())
            .unwrap()
            .cmp(&usize::from_str_radix(&other.number.to_string(), other.base.into()).unwrap())
    }
}

impl ops::Add for Radix {
    type Output = Self;

    /// Performs a `+` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// let res = (n1 + n2).to_radix(8).unwrap();
    /// assert_eq!(res, Radix::from_radix(227, 8).unwrap());
    /// ```

    fn add(self, other: Self) -> Self::Output {
        Self {
            number: Self::from(
                usize::from_str_radix(&self.number.to_string(), self.base.into()).unwrap()
                    + usize::from_str_radix(&other.number.to_string(), other.base.into()).unwrap(),
            )
            .to_radix(self.base)
            .unwrap()
            .number,
            base: self.base,
        }
    }
}

impl ops::AddAssign for Radix {
    /// Performs a `+=` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let mut n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// n1 += n2;
    /// n1 = n1.to_radix(8).unwrap();
    /// assert_eq!(n1, Radix::from_radix(227, 8).unwrap());
    /// ```

    fn add_assign(&mut self, other: Self) {
        self.number = Self::from(
            usize::from_str_radix(&self.number.to_string(), self.base.into()).unwrap()
                + usize::from_str_radix(&other.number.to_string(), other.base.into()).unwrap(),
        )
        .to_radix(self.base)
        .unwrap()
        .number;
    }
}

impl ops::Sub for Radix {
    type Output = Self;

    /// Performs a `-` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// let res = (n1 - n2).to_radix(8).unwrap();
    /// assert_eq!(res, Radix::from_radix(141, 8).unwrap());
    /// ```

    fn sub(self, other: Self) -> Self::Output {
        if self > other {
            Self {
                number: Self::from(
                    usize::from_str_radix(&self.number.to_string(), self.base.into()).unwrap()
                        - usize::from_str_radix(&other.number.to_string(), other.base.into())
                            .unwrap(),
                )
                .to_radix(self.base)
                .unwrap()
                .number,
                base: self.base,
            }
        } else {
            Self {
                number: Self::from(
                    usize::from_str_radix(&other.number.to_string(), other.base.into()).unwrap()
                        - usize::from_str_radix(&self.number.to_string(), self.base.into())
                            .unwrap(),
                )
                .to_radix(other.base)
                .unwrap()
                .number,
                base: other.base,
            }
        }
    }
}

impl ops::Mul for Radix {
    type Output = Self;

    /// Performs a `*` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// let res = (n1 * n2).to_radix(8).unwrap();
    /// assert_eq!(res, Radix::from_radix(6424, 8).unwrap());
    /// ```

    fn mul(self, other: Self) -> Self::Output {
        Self {
            number: Self::from(
                usize::from_str_radix(&self.number.to_string(), self.base.into()).unwrap()
                    * usize::from_str_radix(&other.number.to_string(), other.base.into()).unwrap(),
            )
            .to_radix(self.base)
            .unwrap()
            .number,
            base: self.base,
        }
    }
}

impl ops::MulAssign for Radix {
    /// Performs a `*=` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let mut n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// n1 *= n2;
    /// n1 = n1.to_radix(8).unwrap();
    ///
    /// assert_eq!(n1, Radix::from_radix(6424, 8).unwrap());
    /// ```

    fn mul_assign(&mut self, other: Self) {
        self.number = Self::from(
            usize::from_str_radix(&self.number.to_string(), self.base.into()).unwrap()
                * usize::from_str_radix(&other.number.to_string(), other.base.into()).unwrap(),
        )
        .to_radix(self.base)
        .unwrap()
        .number;
    }
}

impl ops::Div for Radix {
    type Output = Self;

    /// Performs a `/` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// let res = (n2 / n1).to_radix(8).unwrap();
    /// assert_eq!(res, Radix::from_radix(4, 8).unwrap());
    /// ```

    fn div(self, other: Self) -> Self::Output {
        Self {
            number: Self::from(
                usize::from_str_radix(&self.number.to_string(), self.base.into()).unwrap()
                    / usize::from_str_radix(&other.number.to_string(), other.base.into()).unwrap(),
            )
            .to_radix(self.base)
            .unwrap()
            .number,
            base: self.base,
        }
    }
}

impl ops::DivAssign for Radix {
    /// Performs a `/=` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let mut n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// n2 /= n1;
    /// n2 = n2.to_radix(8).unwrap();
    ///
    /// assert_eq!(n2, Radix::from_radix(4, 8).unwrap());
    /// ```

    fn div_assign(&mut self, other: Self) {
        self.number = Self::from(
            usize::from_str_radix(&self.number.to_string(), self.base.into()).unwrap()
                / usize::from_str_radix(&other.number.to_string(), other.base.into()).unwrap(),
        )
        .to_radix(self.base)
        .unwrap()
        .number;
    }
}

impl ops::Rem for Radix {
    type Output = Self;

    /// Performs a `%` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// let res = (n2 % n1).to_radix(8).unwrap();
    /// assert_eq!(res, Radix::from_radix(20, 8).unwrap());
    /// ```

    fn rem(self, other: Self) -> Self::Output {
        Self {
            number: Self::from(
                usize::from_str_radix(&self.number.to_string(), self.base.into()).unwrap()
                    % usize::from_str_radix(&other.number.to_string(), other.base.into()).unwrap(),
            )
            .to_radix(self.base)
            .unwrap()
            .number,
            base: self.base,
        }
    }
}

impl ops::RemAssign for Radix {
    /// Performs a `%=` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let mut n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// n2 %= n1;
    /// n2 = n2.to_radix(8).unwrap();
    ///
    /// assert_eq!(n2, Radix::from_radix(20, 8).unwrap());
    /// ```

    fn rem_assign(&mut self, other: Self) {
        self.number = Self::from(
            usize::from_str_radix(&self.number.to_string(), self.base.into()).unwrap()
                % usize::from_str_radix(&other.number.to_string(), other.base.into()).unwrap(),
        )
        .to_radix(self.base)
        .unwrap()
        .number;
    }
}

/// Radix number, that is usually written as *number*<sub>*base*</sub> (444<sub>8</sub> for
/// example), but number is represented as [`String`] so base could be from range `2..=36`.
/// Fields have the same names as fields of [`Radix`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringRadix {
    pub number: String,
    pub base: u8,
}

impl PartialOrd for StringRadix {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        usize::from_str_radix(&self.number, self.base.into())
            .unwrap()
            .partial_cmp(&usize::from_str_radix(&other.number, other.base.into()).unwrap())
    }
}

impl Ord for StringRadix {
    fn cmp(&self, other: &Self) -> Ordering {
        usize::from_str_radix(&self.number, self.base.into())
            .unwrap()
            .cmp(&usize::from_str_radix(&other.number, other.base.into()).unwrap())
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
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res = (n1 + n2).to_radix(8).unwrap();
    /// assert_eq!(res, StringRadix::from_radix("227", 8).unwrap());
    /// ```

    fn add(self, other: Self) -> Self::Output {
        Self {
            number: Radix::from(
                usize::from_str_radix(&self.number, self.base.into()).unwrap()
                    + usize::from_str_radix(&other.number, other.base.into()).unwrap(),
            )
            .to_str_radix(self.base)
            .unwrap()
            .number,
            base: self.base,
        }
    }
}

impl ops::AddAssign for StringRadix {
    /// Performs a `+=` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let mut n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// n1 += n2;
    /// n1 = n1.to_radix(8).unwrap();
    /// assert_eq!(n1, StringRadix::from_radix("227", 8).unwrap());
    /// ```

    fn add_assign(&mut self, other: Self) {
        self.number = Radix::from(
            usize::from_str_radix(&self.number, self.base.into()).unwrap()
                + usize::from_str_radix(&other.number, other.base.into()).unwrap(),
        )
        .to_str_radix(self.base)
        .unwrap()
        .number;
    }
}

impl ops::Sub for StringRadix {
    type Output = Self;

    /// Performs a `-` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res = (n1 - n2).to_radix(8).unwrap();
    /// assert_eq!(res, StringRadix::from_radix("141", 8).unwrap());
    /// ```

    fn sub(self, other: Self) -> Self::Output {
        if self > other {
            Self {
                number: Radix::from(
                    usize::from_str_radix(&self.number, self.base.into()).unwrap()
                        - usize::from_str_radix(&other.number, other.base.into()).unwrap(),
                )
                .to_str_radix(self.base)
                .unwrap()
                .number,
                base: self.base,
            }
        } else {
            Self {
                number: Radix::from(
                    usize::from_str_radix(&other.number, other.base.into()).unwrap()
                        - usize::from_str_radix(&self.number, self.base.into()).unwrap(),
                )
                .to_str_radix(other.base)
                .unwrap()
                .number,
                base: other.base,
            }
        }
    }
}

impl ops::Mul for StringRadix {
    type Output = Self;

    /// Performs a `*` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res = (n1 * n2).to_radix(8).unwrap();
    /// assert_eq!(res, StringRadix::from_radix("6424", 8).unwrap());
    /// ```

    fn mul(self, other: Self) -> Self::Output {
        Self {
            number: Radix::from(
                usize::from_str_radix(&self.number, self.base.into()).unwrap()
                    * usize::from_str_radix(&other.number, other.base.into()).unwrap(),
            )
            .to_str_radix(self.base)
            .unwrap()
            .number,
            base: self.base,
        }
    }
}

impl ops::MulAssign for StringRadix {
    /// Performs a `*=` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let mut n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// n1 *= n2;
    /// n1 = n1.to_radix(8).unwrap();
    ///
    /// assert_eq!(n1, StringRadix::from_radix("6424", 8).unwrap());
    /// ```

    fn mul_assign(&mut self, other: Self) {
        self.number = Radix::from(
            usize::from_str_radix(&self.number, self.base.into()).unwrap()
                * usize::from_str_radix(&other.number, other.base.into()).unwrap(),
        )
        .to_str_radix(self.base)
        .unwrap()
        .number;
    }
}

impl ops::Div for StringRadix {
    type Output = Self;

    /// Performs a `/` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res = (n2 / n1).to_radix(8).unwrap();
    /// assert_eq!(res, StringRadix::from_radix("4", 8).unwrap());
    /// ```

    fn div(self, other: Self) -> Self::Output {
        Self {
            number: Radix::from(
                usize::from_str_radix(&self.number, self.base.into()).unwrap()
                    / usize::from_str_radix(&other.number, other.base.into()).unwrap(),
            )
            .to_str_radix(self.base)
            .unwrap()
            .number,
            base: self.base,
        }
    }
}

impl ops::DivAssign for StringRadix {
    /// Performs a `/=` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let mut n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// n2 /= n1;
    /// n2 = n2.to_radix(8).unwrap();
    ///
    /// assert_eq!(n2, StringRadix::from_radix("4", 8).unwrap());
    /// ```

    fn div_assign(&mut self, other: Self) {
        self.number = Radix::from(
            usize::from_str_radix(&self.number, self.base.into()).unwrap()
                / usize::from_str_radix(&other.number, other.base.into()).unwrap(),
        )
        .to_str_radix(self.base)
        .unwrap()
        .number;
    }
}

impl ops::Rem for StringRadix {
    type Output = Self;

    /// Performs a `%` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res = (n2 % n1).to_radix(8).unwrap();
    /// assert_eq!(res, StringRadix::from_radix("20", 8).unwrap());
    /// ```

    fn rem(self, other: Self) -> Self::Output {
        Self {
            number: Radix::from(
                usize::from_str_radix(&self.number, self.base.into()).unwrap()
                    % usize::from_str_radix(&other.number, other.base.into()).unwrap(),
            )
            .to_str_radix(self.base)
            .unwrap()
            .number,
            base: self.base,
        }
    }
}

impl ops::RemAssign for StringRadix {
    /// Performs a `%=` operation.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let mut n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// n2 %= n1;
    /// n2 = n2.to_radix(8).unwrap();
    ///
    /// assert_eq!(n2, StringRadix::from_radix("20", 8).unwrap());
    /// ```

    fn rem_assign(&mut self, other: Self) {
        self.number = Radix::from(
            usize::from_str_radix(&self.number, self.base.into()).unwrap()
                % usize::from_str_radix(&other.number, other.base.into()).unwrap(),
        )
        .to_str_radix(self.base)
        .unwrap()
        .number;
    }
}

impl<'a> Radix {
    /// Creates a new [`Radix`].
    ///
    /// # Error
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
    /// assert_eq!(n.number, 0);
    /// assert_eq!(n.base, 2);
    ///
    /// let e1 = Radix::new(1).unwrap_err();
    /// assert_eq!(e1.to_string(), "Base error: base is less than two");
    ///
    /// let e2 = Radix::new(33).unwrap_err();
    /// assert_eq!(e2.to_string(), "Base error: base is more than ten");
    /// ```

    pub fn new(k: u8) -> Result<Self, RadixError<'a>> {
        if k < 2 {
            return Err(RadixError::BaseError("base is less than two"));
        } else if k > 10 {
            return Err(RadixError::BaseError("base is more than ten"));
        } else {
            Ok(Self { number: 0, base: k })
        }
    }

    /// Creates a new [`Radix`] with base 10 and given number.
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::Radix;
    ///
    /// let n = Radix::from(123);
    /// assert_eq!(n.number, 123);
    /// assert_eq!(n.base, 10);
    /// ```

    pub fn from(n: usize) -> Self {
        Self {
            number: n,
            base: 10,
        }
    }

    /// Creates a new [`Radix`] with given number and base.
    ///
    /// # Error
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
    /// assert_eq!(n.number, 11010000);
    /// assert_eq!(n.base, 2);
    ///
    /// let e = Radix::from_radix(444, 3).unwrap_err();
    /// assert_eq!(
    ///     e.to_string(), 
    ///     "Number error: number contains a digit that is more or equal than base",
    /// );
    /// ```

    pub fn from_radix(n: usize, k: u8) -> Result<Self, RadixError<'a>> {
        if k < 2 {
            return Err(RadixError::BaseError("base is less than two"));
        } else if k > 10 {
            return Err(RadixError::BaseError("base is more than ten"));
        } else {
            use super::digit::Digit;

            for i in k..10 {
                if n.has_digit(i) {
                    return Err(RadixError::NumberError(
                        "number contains a digit that is more or equal than base",
                    ));
                }
            }
            Ok(Self { number: n, base: k })
        }
    }

    /// Translate [`Radix`] to another [`Radix`].
    ///
    /// # Panics
    /// Panics if k is less than 2 or k more than 36.
    ///
    /// # Error
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
    /// assert_eq!(new1, Radix::from_radix(173, 8).unwrap());
    /// assert_eq!(new2, Radix::from(123));
    ///
    /// let e = new2.to_radix(1).unwrap_err();
    /// assert_eq!(e.to_string(), "Base error: base is less than two");
    /// ```

    pub fn to_radix(self, k: u8) -> Result<Self, RadixError<'a>> {
        if k < 2 {
            Err(RadixError::BaseError("base is less than two"))
        } else if k > 10 {
            Err(RadixError::BaseError("base is more than ten"))
        } else if self.base == 10 {
            Ok(self.to_radix_from_dec(k)?)
        } else if k == 10 {
            Ok(self.to_dec()?)
        } else {
            Ok(self.to_dec()?.to_radix_from_dec(k)?)
        }
    }

    fn to_dec(self) -> Result<Self, RadixError<'a>> {
        Ok(Radix::from(
            match usize::from_str_radix(&self.number.to_string(), self.base.into()) {
                Ok(n) => n,
                Err(e) => return Err(RadixError::ParseError(e)),
            },
        ))
    }

    fn to_radix_from_dec(mut self, k: u8) -> Result<Self, RadixError<'a>> {
        let mut res = String::new();
        while self.number != 0 {
            res.push(RADIX[self.number % (k as usize)]);
            self.number /= k as usize;
        }
        Radix::from_radix(
            match res.chars().rev().collect::<String>().parse() {
                Ok(n) => n,
                Err(e) => return Err(RadixError::ParseError(e)),
            },
            k,
        )
    }

    /// Translate [`Radix`] to another [`StringRadix`].
    ///
    /// # Panics
    /// Panics if k is less than 2 or k more than 36.
    ///
    /// # Error
    /// Returns a [`BaseError`] when base isn't correct; [`ParseError`] if there was error with
    /// parse functions.
    /// 
    /// [`BaseError`]: RadixError::BaseError
    /// [`ParseError`]: RadixError::ParseError
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::*;
    ///
    /// let n = Radix::from_radix(11010000, 2).unwrap();
    /// let res = n.to_str_radix(16).unwrap();
    /// assert_eq!(res, StringRadix::from_radix("D0", 16).unwrap());
    ///
    /// let e = n.to_str_radix(42).unwrap_err();
    /// assert_eq!(e.to_string(), "Base error: base is more than thirty six (36)");
    /// ```

    pub fn to_str_radix(self, k: u8) -> Result<StringRadix, RadixError<'a>> {
        if k < 2 {
            Err(RadixError::BaseError("base is less than two"))
        } else if k > 36 {
            Err(RadixError::BaseError("base is more than thirty six (36)"))
        } else if self.base == 10 {
            Ok(self.to_str_radix_from_dec(k)?)
        } else if k == 10 {
            Ok(StringRadix::from(&self.to_dec()?.number.to_string())?)
        } else {
            Ok(self.to_dec()?.to_str_radix_from_dec(k)?)
        }
    }

    fn to_str_radix_from_dec(mut self, k: u8) -> Result<StringRadix, RadixError<'a>> {
        let mut res = String::new();
        while self.number != 0 {
            res.push(RADIX[self.number % (k as usize)]);
            self.number /= k as usize;
        }
        StringRadix::from_radix(&res.chars().rev().collect::<String>(), k)
    }

    /// Sum 2 [`Radix`] to new [`StringRadix`].
    ///
    /// # Error
    /// Same as [`to_str_radix`].
    /// 
    /// [`to_str_radix`]: Radix::to_str_radix
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::*;
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// let res = Radix::add_to_str(n1, n2, 16).unwrap();
    /// assert_eq!(res, StringRadix::from_radix("97", 16).unwrap());
    /// ```

    pub fn add_to_str(self, a: Self, k: u8) -> Result<StringRadix, RadixError<'a>> {
        (self + a).to_str_radix(k)
    }

    /// Sub 2 [`Radix`] to new [`StringRadix`].
    ///
    /// # Error
    /// Same as [`to_str_radix`].
    /// 
    /// [`to_str_radix`]: Radix::to_str_radix
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::*;
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// let res = Radix::sub_to_str(n2, n1, 16).unwrap();
    /// assert_eq!(res, StringRadix::from_radix("61", 16).unwrap());
    /// ```

    pub fn sub_to_str(self, a: Self, k: u8) -> Result<StringRadix, RadixError<'a>> {
        (self - a).to_str_radix(k)
    }

    /// Mul 2 [`Radix`] to new [`StringRadix`].
    ///
    /// # Error
    /// Same as [`to_str_radix`].
    /// 
    /// [`to_str_radix`]: Radix::to_str_radix
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::*;
    ///
    /// let n1 = Radix::from_radix(123, 4).unwrap();
    /// let n2 = Radix::from_radix(444, 5).unwrap();
    ///
    /// let res = Radix::mul_to_str(n1, n2, 16).unwrap();
    /// assert_eq!(res, StringRadix::from_radix("D14", 16).unwrap());
    /// ```

    pub fn mul_to_str(self, a: Self, k: u8) -> Result<StringRadix, RadixError<'a>> {
        (self * a).to_str_radix(k)
    }
}

impl<'a> StringRadix {
    /// Creates a new [`StringRadix`].
    ///
    /// # Error
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
    /// assert_eq!(n.number, "0");
    /// assert_eq!(n.base, 2);
    ///
    /// let e1 = StringRadix::new(1).unwrap_err();
    /// assert_eq!(e1.to_string(), "Base error: base is less than two");
    ///
    /// let e2 = StringRadix::new(255).unwrap_err();
    /// assert_eq!(e2.to_string(), "Base error: base is more than thirty six (36)");
    /// ```

    pub fn new(k: u8) -> Result<Self, RadixError<'a>> {
        if k < 2 {
            return Err(RadixError::BaseError("base is less than two"));
        } else if k > 36 {
            return Err(RadixError::BaseError("base is more than thirty six (36)"));
        } else {
            Ok(Self {
                number: String::from("0"),
                base: k,
            })
        }
    }

    /// Creates a new [`StringRadix`] with base 10 and given str number.
    ///
    /// # Error
    /// Return a [`NumberError`] when number contains digit from range `'A'..='Z'`.
    /// 
    /// [`NumberError`]: RadixError::NumberError
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::StringRadix;
    ///
    /// let n = StringRadix::from("123").unwrap();
    /// assert_eq!(n.number, "123");
    /// assert_eq!(n.base, 10);
    ///
    /// let e = StringRadix::from("123A").unwrap_err();
    /// assert_eq!(e.to_string(), "Number error: number contains digit from range `'A'..='Z'`");
    /// ```

    pub fn from(n: &str) -> Result<Self, RadixError<'a>> {
        for i in RADIX.iter().skip(10) {
            if n.contains(*i) {
                return Err(RadixError::NumberError(
                    "number contains digit from range `'A'..='Z'`",
                ));
            }
        }
        Ok(Self {
            number: n.to_string(),
            base: 10,
        })
    }

    /// Creates a new [`StringRadix`] with given number and base.
    ///
    /// # Error
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
    /// assert_eq!(n.number, "11010000");
    /// assert_eq!(n.base, 2);
    ///
    /// let e = StringRadix::from_radix("123A", 9).unwrap_err();
    /// assert_eq!(e.to_string(), "Number error: number contains digit that is more or equal than base");
    /// ```

    pub fn from_radix(n: &str, k: u8) -> Result<Self, RadixError<'a>> {
        if k < 2 {
            return Err(RadixError::BaseError("base is less than two"));
        } else if k > 36 {
            return Err(RadixError::BaseError("base is more than thirty six (36)"));
        } else {
            for i in RADIX.iter().skip(k.into()) {
                if n.contains(*i) {
                    return Err(RadixError::NumberError(
                        "number contains digit that is more or equal than base",
                    ));
                }
            }
            Ok(Self {
                number: n.to_string(),
                base: k,
            })
        }
    }

    /// Translate [`StringRadix`] to another [`StringRadix`].
    ///
    /// # Panics
    /// Panics if k is less than 2 or k more than 36.
    ///
    /// # Error
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
    /// assert_eq!(res, StringRadix::from_radix("D0", 16).unwrap());
    ///
    /// let e = res.to_radix(42).unwrap_err();
    /// assert_eq!(e.to_string(), "Base error: base is more than thirty six (36)");
    /// ```

    pub fn to_radix(&mut self, k: u8) -> Result<Self, RadixError<'a>> {
        if k < 2 {
            return Err(RadixError::BaseError("base is less than two"));
        } else if k > 36 {
            return Err(RadixError::BaseError("base is more than thirty six (36)"));
        } else if k == 10 {
            Ok(Self::from(&self.to_dec()?.number.to_string())?)
        } else if self.base == 10 {
            Ok(Self::from_dec(
                &mut Radix::from(match self.number.parse() {
                    Ok(n) => n,
                    Err(e) => return Err(RadixError::ParseError(e)),
                }),
                k,
            )?)
        } else {
            Ok(Self::from_dec(&mut self.to_dec()?, k)?)
        }
    }

    fn to_dec(&self) -> Result<Radix, RadixError<'a>> {
        Ok(Radix::from(
            match usize::from_str_radix(&self.number, self.base.into()) {
                Ok(n) => n,
                Err(e) => return Err(RadixError::ParseError(e)),
            },
        ))
    }

    fn from_dec(n: &mut Radix, k: u8) -> Result<Self, RadixError<'a>> {
        let mut res = String::new();
        while n.number != 0 {
            res.push(RADIX[n.number % (k as usize)]);
            n.number /= k as usize;
        }
        StringRadix::from_radix(&res.chars().rev().collect::<String>(), k)
    }

    /// Translate [`StringRadix`] to another [`Radix`].
    ///
    /// # Panics
    /// Panics if k is less than 2 or k more than 36.
    ///
    /// # Error
    /// Returns a [`BaseError`] when base isn't correct; [`ParseError`] if there was error with 
    /// parse functions.
    /// 
    /// [`BaseError`]: RadixError::BaseError
    /// [`ParseError`]: RadixError::ParseError
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::*;
    ///
    /// let mut n = StringRadix::from_radix("D14", 16).unwrap();
    /// let res = n.to_int_radix(2).unwrap();
    /// assert_eq!(res, Radix::from_radix(110100010100, 2).unwrap());
    ///
    /// let e = n.to_int_radix(12).unwrap_err();
    /// assert_eq!(e.to_string(), "Base error: base is more than ten");
    /// ```

    pub fn to_int_radix(&mut self, k: u8) -> Result<Radix, RadixError<'a>> {
        if k < 2 {
            return Err(RadixError::BaseError("base is less than two"));
        } else if k > 10 {
            return Err(RadixError::BaseError("base is more than ten"));
        } else if self.base == 10 {
            Ok(Self::from_dec_to_int(
                &mut Radix::from(match self.number.parse() {
                    Ok(n) => n,
                    Err(e) => return Err(RadixError::ParseError(e)),
                }),
                k,
            )?)
        } else if k == 10 {
            Ok(self.to_dec()?)
        } else {
            Ok(Self::from_dec_to_int(&mut self.to_dec()?, k)?)
        }
    }

    fn from_dec_to_int(n: &mut Radix, k: u8) -> Result<Radix, RadixError<'a>> {
        let mut res = String::new();
        while n.number != 0 {
            res.push(RADIX[n.number % (k as usize)]);
            n.number /= k as usize;
        }
        Radix::from_radix(
            match res.chars().rev().collect::<String>().parse() {
                Ok(n) => n,
                Err(e) => return Err(RadixError::ParseError(e)),
            },
            k,
        )
    }

    /// Sum 2 [`StringRadix`] to new [`Radix`].
    ///
    /// # Error
    /// Same as [`to_int_radix`].
    /// 
    /// [`to_int_radix`]: StringRadix::to_int_radix
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::*;
    ///
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res = StringRadix::add_to_int(n1, n2, 8).unwrap();
    /// assert_eq!(res, Radix::from_radix(227, 8).unwrap());
    /// ```

    pub fn add_to_int(self, a: Self, k: u8) -> Result<Radix, RadixError<'a>> {
        (self + a).to_int_radix(k)
    }

    /// Sub 2 [`StringRadix`] to new [`Radix`].
    ///
    /// # Error
    /// Same as [`to_int_radix`].
    /// 
    /// [`to_int_radix`]: StringRadix::to_int_radix
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::*;
    ///
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res = StringRadix::sub_to_int(n2, n1, 8).unwrap();
    /// assert_eq!(res, Radix::from_radix(141, 8).unwrap());
    /// ```

    pub fn sub_to_int(self, a: Self, k: u8) -> Result<Radix, RadixError<'a>> {
        (self - a).to_int_radix(k)
    }

    /// Mul 2 [`StringRadix`] to new [`Radix`].
    ///
    /// # Error
    /// Same as [`to_int_radix`].
    /// 
    /// [`to_int_radix`]: StringRadix::to_int_radix
    ///
    /// # Examples
    ///
    /// ```
    /// use ognlib::num::radix::*;
    ///
    /// let n1 = StringRadix::from_radix("123", 4).unwrap();
    /// let n2 = StringRadix::from_radix("444", 5).unwrap();
    ///
    /// let res = StringRadix::mul_to_int(n1, n2, 8).unwrap();
    /// assert_eq!(res, Radix::from_radix(6424, 8).unwrap());
    /// ```

    pub fn mul_to_int(self, a: Self, k: u8) -> Result<Radix, RadixError<'a>> {
        (self * a).to_int_radix(k)
    }
}
