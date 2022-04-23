use super::{insert_at, move_upper_half};
use std::mem::MaybeUninit;

unsafe fn assume_init(a: &[MaybeUninit<u32>]) -> Vec<u32> {
    a.iter().map(|x| x.assume_init()).collect()
}

#[test]
fn test_move_upper_half_even() {
    let mut source = [0, 1, 2, 3, 4, 5].map(MaybeUninit::new);
    let mut dest = [MaybeUninit::uninit(); 6];
    move_upper_half(&mut source, &mut dest);
    assert_eq!(unsafe { assume_init(&source[0..3]) }, vec![0, 1, 2]);
    assert_eq!(unsafe { assume_init(&dest[0..2]) }, vec![3, 4]);
}

#[test]
fn test_move_upper_half_odd() {
    let mut source = [0, 1, 2, 3, 4].map(MaybeUninit::new);
    let mut dest = [MaybeUninit::uninit(); 5];
    move_upper_half(&mut source, &mut dest);
    assert_eq!(unsafe { assume_init(&source[0..3]) }, vec![0, 1, 2]);
    assert_eq!(unsafe { assume_init(&dest[0..1]) }, vec![3]);
}

#[test]
fn test_insert_at() {
    let mut array = [0, 1, 2, 3, 4, 5, 6].map(MaybeUninit::new);
    let x = insert_at(&mut array, 3, 42);
    assert_eq!(unsafe { x.assume_init() }, 6);
    assert_eq!(unsafe { assume_init(&array) }, [0, 1, 2, 42, 3, 4, 5]);
}

#[test]
fn test_insert_at_last() {
    let mut array = [0, 1, 2].map(MaybeUninit::new);
    let x = insert_at(&mut array, 3, 42);
    assert_eq!(unsafe { x.assume_init() }, 42);
    assert_eq!(unsafe { assume_init(&array) }, [0, 1, 2]);
}
