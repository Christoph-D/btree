use super::{split_insert, BTree, Key, Node};
use rand::{prelude::SliceRandom, thread_rng};
use std::ptr::NonNull;

#[test]
fn test_split_insert_leaf_odd() {
    unsafe {
        let dummy_ptr = Some(NonNull::dangling());
        let node = NonNull::new_unchecked(Box::into_raw(Box::new(Node::<5> {
            keys: [Some(0), Some(1), Some(2), Some(3), Some(4)],
            children: [None; 5],
            next_in_layer: dummy_ptr,
        })));
        let (left, key, right) = split_insert(node, None);
        // split_insert should reuse the provided node.
        assert_eq!(left, node);
        assert_eq!(
            left.as_ref().keys.to_vec(),
            vec![Some(0), Some(1), Some(2), None, None]
        );
        assert_eq!(key, 2);
        assert_eq!(
            right.as_ref().keys.to_vec(),
            vec![Some(3), Some(4), None, None, None]
        );
        assert_eq!(left.as_ref().next_in_layer, Some(right));
        assert_eq!(right.as_ref().next_in_layer, dummy_ptr);
        // Avoid memory leak in tests.
        Box::from_raw(left.as_ptr());
        Box::from_raw(right.as_ptr());
    }
}

#[test]
fn test_split_insert_leaf_even() {
    unsafe {
        let dummy_ptr = Some(NonNull::dangling());
        let node = NonNull::new_unchecked(Box::into_raw(Box::new(Node::<4> {
            keys: [Some(0), Some(1), Some(2), Some(3)],
            children: [None; 4],
            next_in_layer: dummy_ptr,
        })));
        let (left, key, right) = split_insert(node, None);
        // split_insert should reuse the provided node.
        assert_eq!(left, node);
        assert_eq!(
            left.as_ref().keys.to_vec(),
            vec![Some(0), Some(1), None, None]
        );
        assert_eq!(key, 1);
        assert_eq!(
            right.as_ref().keys.to_vec(),
            vec![Some(2), Some(3), None, None]
        );
        assert_eq!(left.as_ref().next_in_layer, Some(right));
        assert_eq!(right.as_ref().next_in_layer, dummy_ptr);
        Box::from_raw(left.as_ptr());
        Box::from_raw(right.as_ptr());
    }
}

#[test]
fn test_simple() {
    let mut tree = BTree::<3>::new();
    tree.insert(1);
    tree.insert(2);
    tree.insert(3);
    assert_eq!(
        format!("{}", tree),
        r#"  [1, 2]
2
  [3]
"#
    );
    assert_eq!(tree.into_iter().collect::<Vec<Key>>(), vec![1, 2, 3]);
}

#[test]
fn test_insert() {
    let mut tree = BTree::<3>::new();
    let mut vec: Vec<u32> = (0..100).collect();
    vec.shuffle(&mut thread_rng());
    for i in vec {
        tree.insert(i);
    }
    for i in 0..100 {
        assert!(tree.lookup(&i), "Not found: {}", i);
    }
    for i in 100..110 {
        assert!(!tree.lookup(&i), "Found: {}", i);
    }
    let r = tree.into_iter().collect::<Vec<Key>>();
    assert_eq!(r, (0..100).collect::<Vec<Key>>());
}

#[test]
fn test_big() {
    let mut tree = BTree::<10>::new();
    let mut vec: Vec<u32> = (0..200).collect();
    vec.shuffle(&mut thread_rng());
    for i in vec {
        tree.insert(i);
    }
    for i in 0..200 {
        assert!(tree.lookup(&i), "Not found: {}", i);
    }
    let r = tree.into_iter().collect::<Vec<Key>>();
    assert_eq!(r, (0..200).collect::<Vec<Key>>());
}
