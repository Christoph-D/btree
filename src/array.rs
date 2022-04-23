//! Functions on arrays.

use std::mem;
use std::mem::MaybeUninit;

#[cfg(test)]
mod test;

/// Moves the upper `M / 2` elements from the source into the destination array,
/// leaving uninitialized values in the old array.
pub(crate) fn move_upper_half<T, const M: usize>(
    source: &mut [MaybeUninit<T>; M],
    dest: &mut [MaybeUninit<T>; M],
) {
    for i in 0..M / 2 {
        dest[i] = mem::replace(&mut source[i + (M + 1) / 2], MaybeUninit::uninit());
    }
}

/// Inserts an item at the given index. Shifts all items starting from this index
/// one step to the right to make space for the new item.
/// Returns the right-most item that got shifted out.
pub(crate) fn insert_at<T, const M: usize>(
    array: &mut [MaybeUninit<T>; M],
    at: usize,
    item: T,
) -> MaybeUninit<T> {
    if at >= M {
        return MaybeUninit::new(item);
    }
    array[at..].rotate_right(1);
    mem::replace(&mut array[at], MaybeUninit::new(item))
}
