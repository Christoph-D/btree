use std::fmt;

/// A B-tree implementation.
#[derive(Debug)]
pub struct BTree<const M: usize> {
    root: Node<M>,
}

type Key = u32;

/// A node in a [BTree].
#[derive(Debug)]
struct Node<const M: usize> {
    /// The number of keys is always the number of children - 1.
    /// Temporarily during modifications a node can be overfull and
    /// contain `M` keys and `M` children, see [InsertResult::Overfull].
    keys: [Option<Key>; M],
    /// The children below this node. Invariants:
    /// * All keys in `children[i]` are smaller than `keys[i]`.
    /// * `keys[i]` is smaller than all keys in `children[i+1]`.
    children: [Option<Box<Node<M>>>; M],
}

impl<const M: usize> Node<M> {
    fn format_with_indent(&self, indent: usize, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_leaf() {
            let keys = self
                .keys
                .iter()
                .flatten()
                .map(|k| k.to_string())
                .collect::<Vec<String>>()
                .join(", ");
            return writeln!(f, "{:indent$}[{keys}]", "", indent = indent, keys = keys);
        }
        for i in 0..M {
            if let Some(child) = &self.children[i] {
                child.format_with_indent(indent + 2, f)?
            }
            if let Some(key) = self.keys[i] {
                writeln!(f, "{:indent$}{key}", "", indent = indent, key = key)?
            }
        }
        Ok(())
    }
}

impl<const M: usize> fmt::Display for BTree<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.root.format_with_indent(0, f)
    }
}

impl<const M: usize> fmt::Display for Node<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.format_with_indent(0, f)
    }
}

#[derive(Debug)]
enum KeyPosition {
    Found,
    /// Index in [`Node::children`].
    InChild(usize),
}

#[derive(Debug)]
enum InsertResult<const M: usize> {
    Inserted,
    /// `Overfull` indicates to the caller that the node needs to be split because it is overfull.
    /// An overfull node has `M` keys (one too many) and `M` children, which is one too few for `M` keys.
    /// The right-most child that didn't fit is carried in this enum.
    Overfull(Option<Box<Node<M>>>),
    AlreadyPresent,
}

/// Split a node into two, inserting the right-most node that didn't previously fit.
/// Returns the newly constructed triple `(left node, key, right node)`.
fn split_insert<const M: usize>(
    mut node: Node<M>,
    node_to_insert_right: Option<Box<Node<M>>>,
) -> (Box<Node<M>>, Key, Box<Node<M>>) {
    let mut new_left = Box::new(Node::new());
    let mut new_right = Box::new(Node::new());

    // Split the node into even halves.
    for i in 0..M / 2 {
        new_left.children[i] = node.children[i].take();
        new_left.keys[i] = node.keys[i];
    }
    new_left.children[M / 2] = node.children[M / 2].take();

    for i in 0..(M - 1) / 2 {
        new_right.children[i] = node.children[i + 1 + M / 2].take();
        new_right.keys[i] = node.keys[i + 1 + M / 2];
    }
    new_right.children[new_right.num_children()] = node_to_insert_right;

    (new_left, node.keys[M / 2].unwrap(), new_right)
}

impl<const M: usize> Node<M> {
    const NO_KEY: Option<u32> = None;
    const NO_NODE: Option<Box<Node<M>>> = None;

    /// Constructs an empty Node with all keys and children set to `None`.
    fn new() -> Node<M> {
        Node {
            keys: [Self::NO_KEY; M],
            children: [Self::NO_NODE; M],
        }
    }

    /// Returns true if this node is a leaf node.
    /// Leaf nodes have no children.
    fn is_leaf(&self) -> bool {
        self.children[0].is_none()
    }

    /// The number of keys in this node.
    fn num_keys(&self) -> usize {
        self.keys.iter().flatten().count()
    }

    /// The number of children in this node. For leaf nodes, this is always 0.
    fn num_children(&self) -> usize {
        self.children.iter().flatten().count()
    }

    /// Locates the given key in this node (not subtree).
    /// For a non-existent key, it returns the InChild value indicating where the key should be inserted.
    fn key_position(&self, key: &Key) -> KeyPosition {
        for i in 0..M {
            match self.keys[i] {
                None => return KeyPosition::InChild(i),
                Some(k) if k > *key => return KeyPosition::InChild(i),
                Some(k) if k == *key => return KeyPosition::Found,
                _ => {}
            }
        }
        unreachable!("Invalid tree: Last key must always be None.");
    }

    /// Returns true if the key is in the subtree starting from this node.
    fn lookup(&self, key: &Key) -> bool {
        match self.key_position(key) {
            KeyPosition::Found => true,
            KeyPosition::InChild(i) => {
                !self.is_leaf() && self.children[i].as_ref().unwrap().lookup(key)
            }
        }
    }

    /// Shift all keys and children starting from and including the given index one to the right.
    /// Returns the right-most node that got shifted out.
    fn shift_right_from(&mut self, from: usize) -> Option<Box<Node<M>>> {
        let right_most = self.children[M - 1].take();
        for i in (from..M - 1).rev() {
            self.children[i + 1] = self.children[i].take();
            self.keys[i + 1] = self.keys[i].take();
        }
        right_most
    }

    /// Insert the given key into the subtree rooted at this node.
    /// Returns [InsertResult::Overfull] if the insertion makes this node overfull.
    /// In this case the node will have `M` keys and `M` children, with an
    /// additional right-most child in the returned enum.
    fn insert(&mut self, key: Key) -> InsertResult<M> {
        // Find out where to insert the new key.
        let key_pos = match self.key_position(&key) {
            KeyPosition::Found => return InsertResult::AlreadyPresent,
            KeyPosition::InChild(i) => i,
        };
        if self.is_leaf() {
            // No need to keep the returned node because leaves have no children.
            self.shift_right_from(key_pos);
            self.keys[key_pos] = Some(key);
            if self.num_keys() == M {
                return InsertResult::Overfull(None);
            }
            return InsertResult::Inserted;
        }
        // Not a leaf. Insert recursively.
        let child_spillover_node = match self.children[key_pos].as_mut().unwrap().insert(key) {
            r @ InsertResult::Inserted | r @ InsertResult::AlreadyPresent => return r,
            InsertResult::Overfull(n) => n,
        };

        // Overfull. Need to split the child node.
        let (new_left_child, pulled_up_key, new_right_child) = split_insert(
            *self.children[key_pos].take().unwrap(),
            child_spillover_node,
        );

        let spillover_node = self.shift_right_from(key_pos);
        self.children[key_pos] = Some(new_left_child);
        self.keys[key_pos] = Some(pulled_up_key);

        // The spillover node is either what we just shifted out or the new right child.
        let spillover_node = if key_pos < M - 1 {
            self.children[key_pos + 1] = Some(new_right_child);
            spillover_node
        } else {
            Some(new_right_child)
        };

        if self.num_keys() == M {
            return InsertResult::Overfull(spillover_node);
        }
        InsertResult::Inserted
    }
}

impl<const M: usize> Default for Node<M> {
    fn default() -> Self {
        Node::new()
    }
}

impl<const M: usize> Default for BTree<M> {
    fn default() -> Self {
        BTree::new()
    }
}

impl<const M: usize> BTree<M> {
    /// Returns a new empty BTree.
    pub fn new() -> BTree<M> {
        BTree {
            root: Default::default(),
        }
    }

    /// Returns true if the key is in the tree.
    pub fn lookup(&self, key: &Key) -> bool {
        self.root.lookup(key)
    }

    /// Inserts the key into the tree.
    pub fn insert(&mut self, key: Key) {
        let spillover_node = match self.root.insert(key) {
            InsertResult::Inserted | InsertResult::AlreadyPresent => return,
            InsertResult::Overfull(node) => node,
        };
        // Split the root.
        let old_root = std::mem::replace(&mut self.root, Node::new());
        let (new_left_child, pulled_up_key, new_right_child) =
            split_insert(old_root, spillover_node);
        self.root.children[0] = Some(new_left_child);
        self.root.keys[0] = Some(pulled_up_key);
        self.root.children[1] = Some(new_right_child);
    }
}

#[cfg(test)]
mod tests {
    use super::{BTree, Node};
    use rand::{prelude::SliceRandom, thread_rng};
    use std::mem::{self, MaybeUninit};

    /// Construct an array with a given prefix.
    fn init_prefix<T, const N: usize>(mut prefix: Vec<T>) -> [Option<T>; N] {
        let mut temp: [MaybeUninit<Option<T>>; N] = unsafe { MaybeUninit::uninit().assume_init() };
        let prefix_length = prefix.len();
        for (i, x) in prefix.drain(..).enumerate() {
            temp[i].write(Some(x));
        }
        for i in prefix_length..N {
            temp[i].write(None);
        }
        unsafe {
            // Workaround for https://github.com/rust-lang/rust/issues/61956.
            let result = (&mut temp as *mut _ as *mut [Option<T>; N]).read();
            mem::forget(temp);
            result
        }
    }

    #[test]
    fn test_lookup() {
        let tree = BTree::<3> {
            root: Node::<3> {
                keys: init_prefix(vec![10, 42]),
                children: init_prefix(vec![
                    Box::<Node<3>>::new(Node::<3> {
                        keys: init_prefix(vec![5]),
                        children: init_prefix(vec![]),
                    }),
                    Box::<Node<3>>::new(Node::<3> {
                        keys: init_prefix(vec![12]),
                        children: init_prefix(vec![]),
                    }),
                    Box::<Node<3>>::new(Node::<3> {
                        keys: init_prefix(vec![50]),
                        children: init_prefix(vec![]),
                    }),
                ]),
            },
        };
        assert_eq!(tree.root.num_keys(), 2);
        assert_eq!(tree.root.num_children(), 3);
        assert!(tree.lookup(&12));
        assert!(!tree.lookup(&15));
        assert!(tree.lookup(&42));
        assert!(!tree.lookup(&43));
        assert!(tree.lookup(&50));
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
    }

    #[test]
    fn test_insert_big() {
        let mut tree = BTree::<20>::new();
        let mut vec: Vec<u32> = (0..1000).collect();
        vec.shuffle(&mut thread_rng());
        for i in vec {
            tree.insert(i);
        }
        for i in 0..1000 {
            assert!(tree.lookup(&i), "Not found: {}", i);
        }
        for i in 1000..1100 {
            assert!(!tree.lookup(&i), "Found: {}", i);
        }
    }
}
