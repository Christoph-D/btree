use super::{split_insert, BTree, Children, Key, Node};
use rand::rngs::StdRng;
use rand::{prelude::SliceRandom, SeedableRng};
use std::ptr::NonNull;

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

unsafe fn data_from_node<Value: Copy, const M: usize>(node: &Node<Value, M>) -> [Option<Value>; M] {
    new_array(|i| {
        match &node.children {
            Children::Nodes(_) => None,
            Children::Data(data) => data[usize::try_from(i).unwrap()].as_ref(),
        }
        .map(|x| **x)
    })
}

#[test]
fn test_split_insert_leaf_odd() {
    unsafe {
        let dummy_ptr = Some(NonNull::dangling());
        let mut left = NonNull::new_unchecked(Box::into_raw(Box::new(Node::<u32, 5> {
            keys: new_array(Some),
            children: Children::Data(new_array(|i| Some(Box::new(i)))),
            next_in_layer: dummy_ptr,
        })));
        let (key, right) = split_insert(left.as_mut(), None);

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
        let mut left = NonNull::new_unchecked(Box::into_raw(Box::new(Node::<u32, 4> {
            keys: new_array(Some),
            children: Children::Data(new_array(|i| Some(Box::new(i)))),
            next_in_layer: dummy_ptr,
        })));
        let (key, right) = split_insert(left.as_mut(), None);

        assert_eq!(
            left.as_ref().keys.to_vec(),
            vec![Some(0), Some(1), None, None]
        );
        assert_eq!(
            data_from_node(left.as_ref()),
            [Some(0), Some(1), None, None]
        );
        assert_eq!(key, 1);
        assert_eq!(
            right.as_ref().keys.to_vec(),
            vec![Some(2), Some(3), None, None]
        );
        assert_eq!(
            data_from_node(right.as_ref()),
            [Some(2), Some(3), None, None]
        );
        assert_eq!(left.as_ref().next_in_layer, Some(right));
        assert_eq!(right.as_ref().next_in_layer, dummy_ptr);

        Box::from_raw(left.as_ptr());
        Box::from_raw(right.as_ptr());
    }
}

#[test]
fn test_simple() {
    let mut tree = BTree::<u32, 3>::new();
    assert!(tree.root_as_ref().is_leaf());
    tree.insert(1, 5);
    tree.insert(2, 6);
    tree.insert(3, 7);
    assert!(!tree.root_as_ref().is_leaf());
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
    let mut tree = BTree::<u32, 3>::new();
    let mut vec: Vec<u32> = (0..100).collect();
    vec.shuffle(&mut StdRng::from_seed([0; 32]));
    for i in vec {
        tree.insert(i, i + 1);
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
    let mut tree = BTree::<u32, 10>::new();
    let mut vec: Vec<u32> = (0..200).collect();
    vec.shuffle(&mut StdRng::from_seed([0; 32]));
    for i in vec {
        tree.insert(i, i + 1);
    }
    for i in 0..200 {
        assert!(tree.lookup(&i), "Not found: {}", i);
    }
    let r = tree.into_iter().collect::<Vec<Key>>();
    assert_eq!(r, (0..200).collect::<Vec<Key>>());
}
