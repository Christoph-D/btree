use std::fmt;
use std::ptr::NonNull;

#[cfg(test)]
mod test;

/// A B-tree implementation.
#[derive(Debug)]
pub struct BTree<const M: usize> {
    root: NodePtr<M>,
}

type Key = u32;
type Value = u32;
type NodePtr<const M: usize> = NonNull<Node<M>>;

#[derive(Debug)]
enum Child<const M: usize> {
    Node(NodePtr<M>),
    Data(Box<Value>),
}

impl<const M: usize> Child<M> {
    fn unwrap_node(&self) -> NodePtr<M> {
        match self {
            Child::Node(node) => *node,
            Child::Data(_) => panic!("Not a node, found data"),
        }
    }

    fn map_nodeptr<F, T>(&self, f: F) -> Option<T>
    where
        F: FnOnce(NodePtr<M>) -> T,
    {
        match self {
            Child::Node(node) => Some(f(*node)),
            Child::Data(_) => None,
        }
    }
}

/// A node in a [BTree].
#[derive(Debug)]
struct Node<const M: usize> {
    /// The number of keys is always the number of children - 1.
    /// Temporarily during modifications a node can be overfull and
    /// contain `M` keys and `M` children, see [InsertResult::Overfull].
    keys: [Option<Key>; M],
    /// The children below this node. Invariants:
    /// * All keys in `children[i]` are smaller or equal to `keys[i]`.
    /// * `keys[i]` is smaller than all keys in `children[i+1]`.
    /// * All keys are copied into the leaf nodes.
    ///   That is, iterating over the leaf nodes yields all keys.
    children: [Option<Child<M>>; M],
    /// The next node in this layer of the tree.
    /// This is `None` for the right-most node in the layer.
    /// Useful for iterating over the leaf nodes.
    next_in_layer: Option<NodePtr<M>>,
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
            if let Some(child) = self.child_node_as_ref(i) {
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
        self.root_as_ref().format_with_indent(0, f)
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
    Overfull(Option<Child<M>>),
    AlreadyPresent,
}

fn new_child_node<const M: usize>() -> NodePtr<M> {
    // SAFETY: A pointer from a Box is never null.
    unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(Node::new()))) }
}

/// Split a node into two, inserting the right-most node that didn't previously fit.
/// Returns the newly constructed triple `(left node, key, right node)`.
/// Reuses the provided `node` as the new left node to keep the previous leaf's `next_in_layer` pointer intact.
/// `node_to_insert_right` must be `None` if and if only `node.is_leaf()` is true.
///
/// SAFETY: The provided child nodes must be valid.
unsafe fn split_insert<const M: usize>(
    mut node: NodePtr<M>,
    node_to_insert_right: Option<Child<M>>,
) -> (NodePtr<M>, Key, NodePtr<M>) {
    // Split the upper half of the node into a new node.
    let mut new_right_ptr = new_child_node();
    let new_right = new_right_ptr.as_mut();
    let old_node = node.as_mut();

    let mut num_children = 0;
    for i in 0..M / 2 {
        if let Some(child) = old_node.children[i + (M + 1) / 2].take() {
            new_right.children[i] = Some(child);
            num_children += 1;
        }
        new_right.keys[i] = old_node.keys[i + (M + 1) / 2].take();
    }
    new_right.children[num_children] = node_to_insert_right;

    new_right.next_in_layer = old_node.next_in_layer;
    old_node.next_in_layer = Some(new_right_ptr);

    let pulled_up_key = if old_node.is_leaf() {
        // Leave a copy of the key in the leaf to ensure all keys are in the leaves.
        old_node.keys[(M - 1) / 2].unwrap()
    } else {
        old_node.keys[(M - 1) / 2].take().unwrap()
    };
    (node, pulled_up_key, new_right_ptr)
}

impl<const M: usize> Node<M> {
    const NO_KEY: Option<u32> = None;
    const NO_NODE: Option<Child<M>> = None;

    /// Constructs an empty Node with all keys and children set to `None`.
    fn new() -> Node<M> {
        Node {
            keys: [Self::NO_KEY; M],
            children: [Self::NO_NODE; M],
            next_in_layer: None,
        }
    }

    /// Applies a function to a child node.
    /// Returns `None` if there is no child node at the given index.
    fn map_child_node<F, T>(&self, i: usize, f: F) -> Option<T>
    where
        F: FnOnce(NodePtr<M>) -> T,
    {
        self.children[i]
            .as_ref()
            .map(|c| c.map_nodeptr(f))
            .flatten()
    }

    /// Returns a pointer to the first child node or `None` if not present.
    fn first_child_node(&self) -> Option<NodePtr<M>> {
        self.map_child_node(0, |c| c)
    }

    /// Returns a child node as an immutable reference.
    fn child_node_as_ref(&self, i: usize) -> Option<&Node<M>> {
        // SAFETY: A child is always a valid pointer or `None`.
        self.map_child_node(i, |c| unsafe { c.as_ref() })
    }

    /// Returns a child node as a mutable reference.
    fn child_node_as_mut(&mut self, i: usize) -> Option<&mut Node<M>> {
        // SAFETY: A child is always a valid pointer or `None`.
        self.map_child_node(i, |mut c| unsafe { c.as_mut() })
    }

    /// Returns true if this node is a leaf node.
    fn is_leaf(&self) -> bool {
        self.map_child_node(0, |_| ()).is_none()
    }

    /// The number of keys in this node.
    fn num_keys(&self) -> usize {
        self.keys.iter().flatten().count()
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
                !self.is_leaf() && self.child_node_as_ref(i).unwrap().lookup(key)
            }
        }
    }

    /// Shift all keys and children starting from and including the given index one to the right.
    /// Returns the right-most node that got shifted out.
    ///
    /// The caller must ensure that the returned `ChildNode` is freed.
    fn shift_right_from(&mut self, from: usize) -> Option<Child<M>> {
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
    ///
    /// The caller must ensure that the returned `ChildNode` in `InsertResult::OverFull` is freed.
    fn insert(&mut self, key: Key, value: Value) -> InsertResult<M> {
        // Find out where to insert the new key.
        let key_pos = match self.key_position(&key) {
            KeyPosition::Found => return InsertResult::AlreadyPresent,
            KeyPosition::InChild(i) => i,
        };
        if self.is_leaf() {
            // No need to keep the returned node because leaves have no children.
            self.shift_right_from(key_pos);
            self.keys[key_pos] = Some(key);
            self.children[key_pos] = Some(Child::Data(Box::new(value)));
            if self.num_keys() == M {
                return InsertResult::Overfull(None);
            }
            return InsertResult::Inserted;
        }
        // Not a leaf. Insert recursively.
        let child_spillover_node = match self.child_node_as_mut(key_pos).unwrap().insert(key, value)
        {
            r @ InsertResult::Inserted | r @ InsertResult::AlreadyPresent => return r,
            InsertResult::Overfull(n) => n,
        };

        // Overfull. Need to split the child node.
        // SAFETY: Both provided nodes are valid.
        let (new_left_child, pulled_up_key, new_right_child) = unsafe {
            split_insert(
                self.children[key_pos].take().unwrap().unwrap_node(),
                child_spillover_node,
            )
        };

        let spillover_node = self.shift_right_from(key_pos);
        self.children[key_pos] = Some(Child::Node(new_left_child));
        self.keys[key_pos] = Some(pulled_up_key);

        // The spillover node is either what we just shifted out or the new right child.
        let spillover_node = if key_pos < M - 1 {
            self.children[key_pos + 1] = Some(Child::Node(new_right_child));
            spillover_node
        } else {
            Some(Child::Node(new_right_child))
        };

        if self.num_keys() == M {
            return InsertResult::Overfull(spillover_node);
        }
        InsertResult::Inserted
    }
}

pub struct IntoIter<const M: usize> {
    _tree: BTree<M>,
    node: NodePtr<M>,
    key_index: usize,
}

impl<const M: usize> std::iter::IntoIterator for BTree<M> {
    type Item = Key;
    type IntoIter = IntoIter<M>;
    fn into_iter(self) -> IntoIter<M> {
        let mut node = self.root;
        // SAFETY: The root is a valid node. Children are always valid nodes.
        while let Some(child) = unsafe { node.as_ref().first_child_node() } {
            node = child;
        }
        IntoIter {
            _tree: self,
            node,
            key_index: 0,
        }
    }
}

impl<const M: usize> Iterator for IntoIter<M> {
    type Item = Key;
    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: self._tree keeps the tree alive including all nodes.
        let node = unsafe { self.node.as_ref() };
        if self.key_index < M - 1 {
            if let Some(key) = node.keys[self.key_index] {
                self.key_index += 1;
                return Some(key);
            }
        }
        if let Some(next) = node.next_in_layer {
            self.node = next;
            self.key_index = 0;
            return self.next();
        }
        None
    }
}

impl<const M: usize> Drop for BTree<M> {
    fn drop(&mut self) {
        // SAFETY: The pointer comes originally from a Box.
        unsafe { Box::from_raw(self.root.as_ptr()) };
    }
}

impl<const M: usize> Drop for Node<M> {
    fn drop(&mut self) {
        for c in self.children.iter().flatten() {
            match c {
                Child::Node(node) => {
                    // SAFETY: The pointer comes originally from a Box.
                    unsafe { Box::from_raw(node.as_ptr()) };
                }
                Child::Data(_) => (),
            }
        }
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
            root: new_child_node(),
        }
    }

    /// Returns an immutable reference to the root node.
    fn root_as_ref(&self) -> &Node<M> {
        // SAFETY: The root is always a valid pointer.
        unsafe { self.root.as_ref() }
    }

    /// Returns a mutable reference to the root node.
    fn root_as_mut(&mut self) -> &mut Node<M> {
        // SAFETY: The root is always a valid pointer.
        unsafe { self.root.as_mut() }
    }

    /// Returns true if the key is in the tree.
    pub fn lookup(&self, key: &Key) -> bool {
        self.root_as_ref().lookup(key)
    }

    /// Inserts the key into the tree.
    pub fn insert(&mut self, key: Key, value: Value) {
        let spillover_node = match self.root_as_mut().insert(key, value) {
            InsertResult::Inserted | InsertResult::AlreadyPresent => return,
            InsertResult::Overfull(node) => node,
        };
        // Split the root and put both parts under a new root.
        let old_root = std::mem::replace(&mut self.root, new_child_node());
        // SAFETY: Both provided nodes are valid.
        let (new_left_child, pulled_up_key, new_right_child) =
            unsafe { split_insert(old_root, spillover_node) };
        let r = self.root_as_mut();
        r.children[0] = Some(Child::Node(new_left_child));
        r.keys[0] = Some(pulled_up_key);
        r.children[1] = Some(Child::Node(new_right_child));
    }
}
