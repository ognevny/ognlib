//! A list of algorithms that is not categorized currently.

/// A binary search algorithm (sorted array is requiered)
/// # Examples
///
/// ```
/// use ognlib::algorithm::extra::bin_search;
///
/// let arr = vec![1, 2, 3, 4, 5];
/// assert_eq!(bin_search(&arr, 2), Some(1));
/// assert_eq!(bin_search(&arr, 6), None);
/// ```

pub fn bin_search<T: Ord>(arr: &[T], targ: T) -> Option<usize> {
    use std::cmp::Ordering;

    let (mut left, mut right) = (0, arr.len() - 1);
    while left <= right {
        let mid = (right + left) / 2;
        match arr[mid].cmp(&targ) {
            Ordering::Equal => return Some(mid),
            Ordering::Greater => right = mid - 1,
            Ordering::Less => left = mid + 1,
        }
    }
    None
}
