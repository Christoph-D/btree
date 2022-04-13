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
enum Children<const M: usize> {
    Nodes([Option<NodePtr<M>>; M]),
    Data([Option<Box<Value>>; M]),
}

impl<const M: usize> Children<M> {
    fn map_nodeptr<F, T>(&self, i: usize, f: F) -> Option<T>
    where
        F: FnOnce(NodePtr<M>) -> T,
    {
        match self {
            Children::Nodes(nodes) => nodes[i].map(f),
            Children::Data(_) => None,
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
    children: Children<M>,
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
    Overfull(Option<NodePtr<M>>),
    AlreadyPresent,
}

fn new_leaf_node<const M: usize>() -> NodePtr<M> {
    // SAFETY: A pointer from a Box is never null.
    unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(Node::new_leaf()))) }
}

fn new_inner_node<const M: usize>() -> NodePtr<M> {
    // SAFETY: A pointer from a Box is never null.
    unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(Node::new_inner()))) }
}

/// Split a node into two, inserting the right-most node that didn't previously fit.
/// Returns the newly constructed triple `(left node, key, right node)`.
/// Reuses the provided `node` as the new left node to keep the previous leaf's `next_in_layer` pointer intact.
/// `item_to_insert_right` must be `None` if and if only if the node is a leaf.
///
/// SAFETY: The provided child nodes must be valid.
unsafe fn split_insert<const M: usize>(
    mut node_ptr: NodePtr<M>,
    item_to_insert_right: Option<NodePtr<M>>,
) -> (NodePtr<M>, Key, NodePtr<M>) {
    // Helper function to move the upper half of an array into a new array.
    fn move_half<T, const M: usize>(
        source: &mut [Option<T>; M],
        dest: &mut [Option<T>; M],
    ) -> usize {
        let mut num_nonempty = 0;
        for i in 0..M / 2 {
            if let Some(x) = source[i + (M + 1) / 2].take() {
                dest[i] = Some(x);
                num_nonempty += 1;
            }
        }
        num_nonempty
    }

    let node = node_ptr.as_mut();
    // Create a new sibling and move half of the children to it.
    let (pulled_up_key, mut new_right_ptr) = match &mut node.children {
        Children::Nodes(nodes) => {
            // node is an inner node.
            let mut new_right_ptr = new_inner_node();
            let new_children = new_right_ptr.as_mut().children_nodes_mut().unwrap();
            let num_children = move_half(nodes, new_children);
            new_children[num_children] = item_to_insert_right;
            (
                // Take the key out of the inner node. Only leaf nodes get copies of keys.
                node.keys[(M - 1) / 2].take().unwrap(),
                new_right_ptr,
            )
        }
        Children::Data(data) => {
            // node is a leaf node.
            let mut new_right_ptr = new_leaf_node();
            move_half(data, new_right_ptr.as_mut().children_data_mut().unwrap());
            // Copy the key out of the leaf to ensure all keys are present in the leaves.
            (node.keys[(M - 1) / 2].unwrap(), new_right_ptr)
        }
    };

    // Move half of the keys to the new node.
    move_half(&mut node.keys, &mut new_right_ptr.as_mut().keys);

    // Fix the intra-layer pointers.
    new_right_ptr.as_mut().next_in_layer = node.next_in_layer;
    node.next_in_layer = Some(new_right_ptr);

    (node_ptr, pulled_up_key, new_right_ptr)
}

impl<const M: usize> Node<M> {
    const NO_KEY: Option<u32> = None;
    const NO_NODE: Option<NodePtr<M>> = None;
    const NO_DATA: Option<Box<Value>> = None;

    /// Constructs an empty leaf Node with all keys and children set to `None`.
    fn new_leaf() -> Node<M> {
        Node {
            keys: [Self::NO_KEY; M],
            children: Children::Data([Self::NO_DATA; M]),
            next_in_layer: None,
        }
    }

    /// Constructs an empty inner Node with all keys and children set to `None`.
    fn new_inner() -> Node<M> {
        Node {
            keys: [Self::NO_KEY; M],
            children: Children::Nodes([Self::NO_NODE; M]),
            next_in_layer: None,
        }
    }

    /// Returns a mutable reference to the child nodes or `None` if this is a leaf node.
    fn children_nodes_mut(&mut self) -> Option<&mut [Option<NodePtr<M>>; M]> {
        match &mut self.children {
            Children::Nodes(nodes) => Some(nodes),
            Children::Data(_) => None,
        }
    }

    /// Returns a mutable reference to the data entries or `None` if this is an inner node.
    fn children_data_mut(&mut self) -> Option<&mut [Option<Box<u32>>; M]> {
        match &mut self.children {
            Children::Nodes(_) => None,
            Children::Data(data) => Some(data),
        }
    }

    /// Returns a pointer to the first child node or `None` if not present.
    fn first_child_node(&self) -> Option<NodePtr<M>> {
        self.children.map_nodeptr(0, |c| c)
    }

    /// Returns a child node as an immutable reference.
    fn child_node_as_ref(&self, i: usize) -> Option<&Node<M>> {
        // SAFETY: A child is always a valid pointer or `None`.
        self.children.map_nodeptr(i, |c| unsafe { c.as_ref() })
    }

    /// Returns true if this node is a leaf node.
    fn is_leaf(&self) -> bool {
        self.first_child_node().is_none()
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
    /// The caller must ensure that the returned node is freed.
    fn shift_right_from<T>(
        keys: &mut [Option<Key>; M],
        children: &mut [Option<T>; M],
        from: usize,
    ) -> Option<T> {
        let right_most = children[M - 1].take();
        for i in (from..M - 1).rev() {
            children[i + 1] = children[i].take();
            keys[i + 1] = keys[i].take();
        }
        right_most
    }

    /// Insert the given key into the subtree rooted at this node.
    /// Returns [InsertResult::Overfull] if the insertion makes this node overfull.
    /// In this case the node will have `M` keys and `M` children, with an
    /// additional right-most child in the returned enum.
    ///
    /// The caller must ensure that the returned node in `InsertResult::Overfull` is freed.
    fn insert(&mut self, key: Key, value: Value) -> InsertResult<M> {
        // Find out where to insert the new key.
        let key_pos = match self.key_position(&key) {
            KeyPosition::Found => return InsertResult::AlreadyPresent,
            KeyPosition::InChild(i) => i,
        };
        let nodes = match &mut self.children {
            Children::Data(data) => {
                Node::<M>::shift_right_from(&mut self.keys, data, key_pos);
                self.keys[key_pos] = Some(key);
                data[key_pos] = Some(Box::new(value));
                if self.num_keys() == M {
                    return InsertResult::Overfull(None);
                }
                return InsertResult::Inserted;
            }
            Children::Nodes(nodes) => nodes,
        };
        // Not a leaf. Insert recursively.
        // SAFETY: A child is always a valid pointer or `None`. In this case it's not `None` because
        // an inner node always has a child to the right of each key.
        let spillover_content = match unsafe { nodes[key_pos].unwrap().as_mut().insert(key, value) }
        {
            r @ InsertResult::Inserted | r @ InsertResult::AlreadyPresent => return r,
            InsertResult::Overfull(n) => n,
        };

        // Overfull. Need to split the child node.
        // SAFETY: Both provided nodes are valid.
        let (new_left_child, pulled_up_key, new_right_child) =
            unsafe { split_insert(nodes[key_pos].take().unwrap(), spillover_content) };

        let spillover_node = Node::<M>::shift_right_from(&mut self.keys, nodes, key_pos);
        nodes[key_pos] = Some(new_left_child);
        self.keys[key_pos] = Some(pulled_up_key);

        // The spillover node is either what we just shifted out or the new right child.
        let spillover_node = if key_pos < M - 1 {
            nodes[key_pos + 1] = Some(new_right_child);
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
        match self.children {
            Children::Nodes(nodes) => {
                for c in nodes.iter().flatten() {
                    // SAFETY: The pointer comes originally from a Box.
                    unsafe { Box::from_raw(c.as_ptr()) };
                }
            }
            Children::Data(_) => (),
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
            root: new_leaf_node(),
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
        let old_root = std::mem::replace(&mut self.root, new_inner_node());
        // SAFETY: Both provided nodes are valid.
        let (new_left_child, pulled_up_key, new_right_child) =
            unsafe { split_insert(old_root, spillover_node) };
        let r = self.root_as_mut();
        let nodes = r.children_nodes_mut().unwrap();
        nodes[0] = Some(new_left_child);
        nodes[1] = Some(new_right_child);
        r.keys[0] = Some(pulled_up_key);
    }
}
