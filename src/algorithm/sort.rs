//! Some sort algorithmes

// TODO: write a code for more sorts.

/// Bubble sort algorithm.
/// # Examples
///
/// ```
/// use ognlib::algorithm::sort::bubble;
///
/// let mut arr = vec![5, 3, 4, 1, 2];
/// bubble(&mut arr);
/// assert_eq!(arr, [1, 2, 3, 4, 5]);
/// ```

pub fn bubble<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    let mut swapped = false;
    for i in 0..n {
        for j in 0..n - i - 1 {
            if arr[j] > arr[j + 1] {
                arr.swap(j + 1, j);
                swapped = true;
            }
        }
        if !swapped {
            break;
        }
    }
}

/// Search sort algorithm.
/// # Examples
///
/// ```
/// use ognlib::algorithm::sort::search;
///
/// let mut arr = vec![5, 3, 4, 1, 2];
/// search(&mut arr);
/// assert_eq!(arr, [1, 2, 3, 4, 5]);
/// ```

pub fn search<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    for i in 0..n - 1 {
        let mut i_min = i;
        for j in i + 1..n {
            if arr[j] < arr[i_min] {
                i_min = j
            }
        }
        if i_min != i {
            arr.swap(i, i_min)
        }
    }
}

/// Insertion sort algorithm.
/// # Examples
///
/// ```
/// use ognlib::algorithm::sort::insertion;
///
/// let mut arr = vec![5, 3, 4, 1, 2];
/// insertion(&mut arr);
/// assert_eq!(arr, [1, 2, 3, 4, 5]);
/// ```

pub fn insertion<T: Ord>(arr: &mut [T]) {
    for i in 1..arr.len() {
        let key = &arr[i];
        let mut j = i;
        let pos = arr[..i].binary_search(key).unwrap_or_else(|pos| pos);
        while j > pos {
            arr.swap(j - 1, j);
            j -= 1;
        }
    }
}

/// Merge sort algorithm.
/// # Examples
///
/// ```
/// use ognlib::algorithm::sort::merge;
///
/// let mut arr = vec![5, 3, 4, 1, 2];
/// merge(&mut arr);
/// assert_eq!(arr, [1, 2, 3, 4, 5]);
/// ```

pub fn merge<T>(slice: &mut [T])
where T: Ord + Clone + Copy + Send + Sync {
    let len = slice.len();
    if len < 2 {
        return;
    }
    let mid = len / 2;
    let (left, right) = slice.split_at_mut(mid);

    rayon::join(|| merge(left), || merge(right));

    merging(slice);
}

fn merging<S, T>(slice: &mut S)
where
    S: AsMut<[T]> + AsRef<[T]> + Sync + Send + ?Sized,
    T: Ord + Clone + Send + Copy,
{
    let len = slice.as_ref().len();
    if len < 2 {
        return;
    }
    let mid = len / 2;
    let (left, right) = slice.as_ref().split_at(mid);
    let mut buffer = Vec::with_capacity(len);
    let (mut i, mut j) = (0, 0);

    while i < mid && j < len - mid {
        if left[i] < right[j] {
            buffer.push(left[i]);
            i += 1;
        } else {
            buffer.push(right[j]);
            j += 1;
        }
    }
    if i < mid {
        buffer.extend_from_slice(&left[i..]);
    }
    if j < len - mid {
        buffer.extend_from_slice(&right[j..]);
    }
    slice.as_mut().copy_from_slice(&buffer);
}

/// Cocktail shaker sort algorithm.
/// # Examples
///
/// ```
/// use ognlib::algorithm::sort::cocktail_shaker;
///
/// let mut arr = vec![5, 3, 4, 1, 2];
/// cocktail_shaker(&mut arr);
/// assert_eq!(arr, [1, 2, 3, 4, 5]);
/// ```

pub fn cocktail_shaker<T: Ord>(arr: &mut [T]) {
    let (mut swapped, mut left, mut right) = (true, 0, arr.len() - 1);

    while swapped {
        swapped = false;

        for i in left..right {
            if arr[i] > arr[i + 1] {
                arr.swap(i, i + 1);
                swapped = true;
            }
        }
        if !swapped {
            break;
        }
        swapped = false;

        right -= 1;
        for i in (left..right).rev() {
            if arr[i] > arr[i + 1] {
                arr.swap(i, i + 1);
                swapped = true;
            }
        }
        left += 1;
    }
}

/// Quick sort algorithm.
/// # Examples
///
/// ```
/// use ognlib::algorithm::sort::quick;
///
/// let mut arr = vec![5, 3, 4, 1, 2];
/// quick(&mut arr);
/// assert_eq!(arr, [1, 2, 3, 4, 5]);
/// ```

pub fn quick<T>(arr: &mut [T])
where T: Ord + Send + Clone {
    if arr.len() <= 1 {
        return;
    }
    let pivot = partition(arr);
    let (left, right) = arr.split_at_mut(pivot);

    rayon::join(|| quick(left), || quick(right));
}

fn partition<T>(arr: &mut [T]) -> usize
where T: Ord + Send + Clone {
    let len = arr.len();
    let pivot_index = len / 2;
    let pivot = arr[pivot_index].clone();

    let mut i = 0;
    let mut j = len - 1;
    loop {
        while arr[i] < pivot {
            i += 1;
        }
        while arr[j] > pivot {
            j -= 1;
        }
        if i >= j {
            return j;
        }
        arr.swap(i, j);
    }
}
