//! Functions on arrays.

use std::mem;

#[cfg(test)]
mod test;

/// Moves the upper `M / 2 - 1` elements from the source into the destination array,
/// leaving default values in the old array.
pub(crate) fn move_upper_half<T: Default, const M: usize>(source: &mut [T; M], dest: &mut [T; M]) {
    for i in 0..M / 2 {
        dest[i] = mem::take(&mut source[i + (M + 1) / 2]);
    }
}

/// Inserts an item at the given index. Shifts all items starting from this index
/// one step to the right to make space for the new item.
/// Returns the right-most item that got shifted out.
pub(crate) fn insert_at<T, const M: usize>(array: &mut [T; M], at: usize, item: T) -> T {
    if at >= M {
        return item;
    }
    array[at..].rotate_right(1);
    mem::replace(&mut array[at], item)
}
