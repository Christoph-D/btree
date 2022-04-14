use super::{insert_at, move_upper_half};

#[test]
fn test_move_upper_half_even() {
    let mut source = [Some(0), Some(1), Some(2), Some(3), Some(4), None];
    let mut dest = [None; 6];
    move_upper_half(&mut source, &mut dest);
    assert_eq!(source, [Some(0), Some(1), Some(2), None, None, None]);
    assert_eq!(dest, [Some(3), Some(4), None, None, None, None]);
}

#[test]
fn test_move_upper_half_odd() {
    let mut source = [Some(0), Some(1), Some(2), Some(3), None];
    let mut dest = [None; 5];
    move_upper_half(&mut source, &mut dest);
    assert_eq!(source, [Some(0), Some(1), Some(2), None, None]);
    assert_eq!(dest, [Some(3), None, None, None, None]);
}

#[test]
fn test_insert_at() {
    let mut array = [0, 1, 2, 3, 4, 5, 6];
    let x = insert_at(&mut array, 3, 42);
    assert_eq!(x, 6);
    assert_eq!(array, [0, 1, 2, 42, 3, 4, 5]);
}

#[test]
fn test_insert_at_last() {
    let mut array = [0, 1, 2];
    let x = insert_at(&mut array, 3, 42);
    assert_eq!(x, 42);
    assert_eq!(array, [0, 1, 2]);
}
