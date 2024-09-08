//! A list of algorithms that is not categorized currently.

use core::cmp::Ordering;

extern crate alloc;
#[cfg(all(feature = "rayon"))]
use {
    alloc::{borrow::ToOwned, string::ToString, vec::Vec},
    rayon::prelude::*,
    regex::Regex,
};

/// A binary search algorithm (sorted array is requiered).
/// # Examples
///
/// ```
/// use ognlib::algorithm::extra::bin_search;
///
/// let arr = vec![1, 2, 3, 4, 5];
/// assert_eq!(bin_search(&arr, &2), Some(1));
/// assert_eq!(bin_search(&arr, &6), None);
/// ```
pub fn bin_search<T: Ord>(arr: &[T], targ: &T) -> Option<usize> {
    let (mut left, mut right) = (0, arr.len() - 1);
    while left <= right {
        let mid = (right + left) / 2;
        match arr.get(mid)?.cmp(targ) {
            Ordering::Equal => return Some(mid),
            Ordering::Greater => right = mid - 1,
            Ordering::Less => left = mid + 1,
        }
    }
    None
}

/// Russian informatics exam has a task that asks you to find the numbers, that matches the "mask"
/// (for example "123*567?") between lower and upper bounds. Actually, this is not full
/// implementation, as this also has external condition.
///
/// # Panics
/// panics if lower bound is greater than lower bound
///
/// # Example
///
/// ```
/// use ognlib::algorithm::extra::mask_match;
///
/// let nums1 = mask_match(100, 200, "1?0");
/// assert_eq!(nums1, vec![100, 110, 120, 130, 140, 150, 160, 170, 180, 190]);
///
/// let nums2 = mask_match(1, 10, "*");
/// assert_eq!(nums2, vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
/// ```
///
/// If you wish to apply extra conditions, you can use power of [`Iterator`] for this. Then boost
/// the proccess a bit using [`rayon`].
///
/// ```
/// use {ognlib::algorithm::extra::mask_match, rayon::prelude::*};
///
/// let nums_div_by_169: Vec<usize> =
///     mask_match(1, 1000000000, "123*567?").into_par_iter().filter(|&x| x % 169 == 0).collect();
///
/// assert_eq!(nums_div_by_169, vec![
///     12325677, 12385672, 123157567, 123165679, 123225674, 123326567, 123495567, 123515678,
///     123575673, 123664567, 123833567, 123865677, 123925672,
/// ])
/// ```
#[cfg(all(feature = "rayon"))]
#[must_use]
pub fn mask_match(lower: usize, upper: usize, mask: &str) -> Vec<usize> {
    assert!(lower <= upper, "lower bound can't be greater than upper bound");

    let mut re = "^".to_owned();
    re.push_str(&mask.replace('*', ".*").replace('?', ".?"));
    re.push('$');
    let re = Regex::new(&re).unwrap();
    (lower..=upper).into_par_iter().filter(|num| re.is_match(&num.to_string())).collect()
}
