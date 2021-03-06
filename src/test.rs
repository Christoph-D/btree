use super::{drop_node, split_insert, BTree, LeafNode};
use rand::rngs::StdRng;
use rand::{prelude::SliceRandom, SeedableRng};
use std::mem::MaybeUninit;
use std::ptr::NonNull;

type Key = u32;

fn new_array<F, T, const M: usize>(f: F) -> [T; M]
where
    F: Fn(u32) -> T,
{
    let mut i: u32 = 0;
    [(); M].map(|_| {
        let t = f(i);
        i += 1;
        t
    })
}

unsafe fn data_from_node<K, V: Copy, const M: usize>(node: &LeafNode<K, V, M>) -> Vec<V> {
    node.data[0..node.num_keys]
        .iter()
        .map(|x| *x.assume_init_ref())
        .collect()
}

#[test]
fn test_split_insert_leaf_odd() {
    unsafe {
        let dummy_ptr = Some(NonNull::dangling());
        let mut left = LeafNode::<Key, u32, 5> {
            num_keys: 5,
            keys: new_array(MaybeUninit::new),
            data: new_array(|i| MaybeUninit::new(i)),
            next_in_layer: dummy_ptr,
        }
        .leak_from_box();
        let (key, right) = split_insert(left.as_mut(), None);

        assert_eq!(
            left.as_ref().keys().copied().collect::<Vec<Key>>(),
            vec![0, 1, 2]
        );
        assert_eq!(key, 2);
        assert_eq!(
            right.as_ref().keys().copied().collect::<Vec<Key>>(),
            vec![3, 4]
        );
        assert_eq!(left.as_ref().leaf.next_in_layer, Some(right));
        assert_eq!(right.as_ref().leaf.next_in_layer, dummy_ptr);

        // Avoid memory leak in tests.
        drop_node(0, left);
        drop_node(0, right);
    }
}

#[test]
fn test_split_insert_leaf_even() {
    unsafe {
        let dummy_ptr = Some(NonNull::dangling());
        let mut left = LeafNode::<Key, u32, 4> {
            keys: new_array(MaybeUninit::new),
            num_keys: 4,
            data: new_array(|i| MaybeUninit::new(i)),
            next_in_layer: dummy_ptr,
        }
        .leak_from_box();
        let (key, right) = split_insert(left.as_mut(), None);

        let left_leaf = &left.as_ref().leaf;
        let right_leaf = &right.as_ref().leaf;

        assert_eq!(
            left.as_ref().keys().copied().collect::<Vec<Key>>(),
            vec![0, 1]
        );
        assert_eq!(data_from_node(left_leaf), [0, 1]);
        assert_eq!(key, 1);
        assert_eq!(
            right.as_ref().keys().copied().collect::<Vec<Key>>(),
            vec![2, 3]
        );
        assert_eq!(data_from_node(right_leaf), [2, 3]);
        assert_eq!(left_leaf.next_in_layer, Some(right));
        assert_eq!(right_leaf.next_in_layer, dummy_ptr);

        // Avoid memory leak in tests.
        drop_node(0, left);
        drop_node(0, right);
    }
}

#[test]
fn test_simple() {
    let mut tree = BTree::<Key, u32, 3>::new();
    tree.insert(1, 5);
    tree.insert(2, 6);
    tree.insert(3, 7);
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
fn test_simple_even() {
    let mut tree = BTree::<Key, u32, 4>::new();
    tree.insert(1, 5);
    tree.insert(2, 6);
    tree.insert(3, 7);
    tree.insert(4, 9);
    assert_eq!(
        format!("{}", tree),
        r#"  [1, 2]
2
  [3, 4]
"#
    );
    assert_eq!(tree.into_iter().collect::<Vec<Key>>(), vec![1, 2, 3, 4]);
}

#[test]
fn test_string_keys() {
    let mut tree = BTree::<String, u32, 4>::new();
    tree.insert("five".to_owned(), 5);
    tree.insert("six".to_owned(), 6);
    tree.insert("seven".to_owned(), 7);
    tree.insert("four".to_owned(), 9);
    assert!(tree.contains_key("six"));
    assert!(!tree.contains_key("twenty"));
    assert_eq!(tree.get("six").copied(), Some(6));
    assert_eq!(tree.get("twenty").copied(), None);
}

#[test]
fn test_insert() {
    let mut tree = BTree::<Key, u32, 3>::new();
    let mut vec: Vec<u32> = (0..100).collect();
    vec.shuffle(&mut StdRng::from_seed([0; 32]));
    for i in vec {
        tree.insert(i, i + 1);
    }
    for i in 0..100 {
        assert!(tree.contains_key(&i), "Not found: {}", i);
        assert_eq!(tree.get(&i).copied(), Some(i + 1), "Not found: {}", i);
    }
    for i in 100..110 {
        assert!(!tree.contains_key(&i), "Found: {}", i);
        assert_eq!(tree.get(&i), None, "Found: {}", i);
    }
    let r = tree.into_iter().collect::<Vec<Key>>();
    assert_eq!(r, (0..100).collect::<Vec<Key>>());
}

#[test]
fn test_big() {
    let mut tree = BTree::<Key, u32, 10>::new();
    let mut vec: Vec<u32> = (0..200).collect();
    vec.shuffle(&mut StdRng::from_seed([0; 32]));
    for i in vec {
        tree.insert(i, i + 1);
    }
    for i in 0..200 {
        assert!(tree.contains_key(&i), "Not found: {}", i);
        assert_eq!(tree.get(&i).copied(), Some(i + 1), "Not found: {}", i);
    }
    let r = tree.into_iter().collect::<Vec<Key>>();
    assert_eq!(r, (0..200).collect::<Vec<Key>>());
}
