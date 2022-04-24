use array::{insert_at, move_upper_half};
use std::borrow::Borrow;
use std::fmt;
use std::marker::PhantomData;
use std::mem::{self, MaybeUninit};
use std::ptr::NonNull;

mod array;

#[cfg(test)]
mod test;

/// A B+ tree implementation.
#[derive(Debug)]
pub struct BTree<K, V, const M: usize> {
    root: NodePtr<K, V, M>,
    /// The number of layers in this tree minus 1.
    /// An empty tree consisting only of a root node has height 0.
    height: usize,
}

type NodePtr<K, V, const M: usize> = NonNull<InnerOrLeafNode<K, V, M>>;

/// An inner or leaf node node in a [BTree]. Layout-compatible with [InnerNode] and [LeafNode].
#[derive(Debug)]
#[repr(C)]
struct InnerOrLeafNode<K, V, const M: usize> {
    /// The number of keys is always the number of children - 1.
    /// Temporarily during modifications a node can be overfull and
    /// contain `M` keys and `M` children, see [InsertResult::Overfull].
    keys: [MaybeUninit<K>; M],
    // The number of keys.
    num_keys: usize,

    _data_marker: PhantomData<V>,
}

/// An inner node in a [BTree]. Prefix layout-compatible with [LeafNode].
#[derive(Debug)]
#[repr(C)]
struct InnerNode<K, V, const M: usize> {
    /// The number of keys is always the number of children - 1.
    /// Temporarily during modifications a node can be overfull and
    /// contain `M` keys and `M` children, see [InsertResult::Overfull].
    keys: [MaybeUninit<K>; M],
    // The number of keys.
    num_keys: usize,
    /// The children below this node. Invariants:
    /// * All keys in `children[i]` are smaller or equal to `keys[i]`.
    /// * `keys[i]` is smaller than all keys in `children[i+1]`.
    /// * All keys are copied into the leaf nodes.
    ///   That is, iterating over the leaf nodes yields all keys.
    children: [MaybeUninit<NodePtr<K, V, M>>; M],

    _data_marker: PhantomData<V>,
}

/// A leaf node in a [BTree]. Prefix layout-compatible with [InnerNode].
#[derive(Debug)]
#[repr(C)]
struct LeafNode<K, V, const M: usize> {
    /// The number of keys is always the number of children - 1.
    /// Temporarily during modifications a node can be overfull and
    /// contain `M` keys and `M` children, see [InsertResult::Overfull].
    keys: [MaybeUninit<K>; M],
    // The number of keys.
    num_keys: usize,
    /// The data in this node. `key[i]` maps to `data[i]`.
    data: [MaybeUninit<V>; M],
    /// The next node in this layer of the tree.
    /// This is `None` for the right-most node in the layer.
    /// Useful for iterating over the leaf nodes.
    next_in_layer: Option<NodePtr<K, V, M>>,
}

impl<K, V, const M: usize> InnerOrLeafNode<K, V, M>
where
    K: std::fmt::Display,
{
    // SAFETY: The provided height must be correct.
    // Specifically, self must be a leaf if and only if height is zero.
    unsafe fn format_with_indent(
        &self,
        height: usize,
        indent: usize,
        f: &mut fmt::Formatter,
    ) -> fmt::Result {
        if InnerOrLeafNode::<K, V, M>::is_leaf(height) {
            let keys = self
                .keys()
                .map(|k| format!("{}", k))
                .collect::<Vec<String>>()
                .join(", ");
            return writeln!(f, "{:indent$}[{keys}]", "", indent = indent, keys = keys);
        }
        let inner_node = self.as_inner_node();
        for i in 0..self.num_keys + 1 {
            let child = inner_node.children[i].assume_init().as_ref();
            child.format_with_indent(height - 1, indent + 2, f)?;
            if i < self.num_keys {
                writeln!(
                    f,
                    "{:indent$}{key}",
                    "",
                    indent = indent,
                    key = self.keys[i].assume_init_ref()
                )?
            }
        }
        Ok(())
    }
}

impl<K, V, const M: usize> fmt::Display for BTree<K, V, M>
where
    K: std::fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        unsafe { self.root_as_ref().format_with_indent(self.height, 0, f) }
    }
}

#[derive(Debug)]
enum KeyPosition {
    /// Index in [`InnerOrLeafNode::keys`].
    Found(usize),
    /// Index in [`InnerNode::children`] or [`LeafNode::data`].
    InChild(usize),
}

#[derive(Debug)]
enum InsertResult<K, V, const M: usize> {
    Inserted,
    /// `Overfull` indicates to the caller that the node needs to be split because it is overfull.
    /// An overfull node has `M` keys (one too many) and `M` children, which is one too few for `M` keys.
    /// The right-most child that didn't fit is carried in this enum.
    Overfull(Option<NodePtr<K, V, M>>),
    AlreadyPresent,
}

/// Split a node into two, inserting the right-most node that didn't previously fit.
///
/// Returns the newly constructed pair `(key, right node)`.
/// Reuses the provided `node` as the new left node to keep the previous leaf's `next_in_layer` pointer intact.
/// `item_to_insert_right` must be `None` if and if only if the node is a leaf.
unsafe fn split_insert<K, V, const M: usize>(
    left: &mut InnerOrLeafNode<K, V, M>,
    item_to_insert_right: Option<NodePtr<K, V, M>>,
) -> (K, NodePtr<K, V, M>)
where
    K: Clone,
{
    match item_to_insert_right {
        None => leaf_split_insert(left.as_leaf_node_mut()),
        Some(item) => inner_split_insert(left.as_inner_node_mut(), item),
    }
}

unsafe fn inner_split_insert<K, V, const M: usize>(
    left: &mut InnerNode<K, V, M>,
    item_to_insert_right: NodePtr<K, V, M>,
) -> (K, NodePtr<K, V, M>) {
    // Create a new sibling and move half of the children to it.
    let mut right = Box::new(InnerNode::new());
    move_upper_half(&mut left.children, &mut right.children);
    right.children[M / 2].write(item_to_insert_right);
    let pulled_up_key =
        mem::replace(&mut left.keys[(M - 1) / 2], MaybeUninit::uninit()).assume_init();

    // Move half of the keys to the new node.
    move_upper_half(&mut left.keys, &mut right.keys);
    left.num_keys = (M - 1) / 2;
    right.num_keys = M / 2;

    (pulled_up_key, right.leak_from_box())
}

unsafe fn leaf_split_insert<K, V, const M: usize>(
    left: &mut LeafNode<K, V, M>,
) -> (K, NodePtr<K, V, M>)
where
    K: Clone,
{
    // Create a new sibling and move half of the children to it.
    let mut right = Box::new(LeafNode::new());
    move_upper_half(&mut left.data, &mut right.data);
    // Copy the key out of the leaf to ensure all keys are present in the leaves.
    let pulled_up_key = left.keys[(M - 1) / 2].assume_init_ref().clone();

    // Move half of the keys to the new node.
    move_upper_half(&mut left.keys, &mut right.keys);
    left.num_keys = (M + 1) / 2;
    right.num_keys = M / 2;

    // Fix the intra-layer pointers.
    right.next_in_layer = left.next_in_layer;
    let new_right_ptr = right.leak_from_box();
    left.next_in_layer = Some(new_right_ptr);

    (pulled_up_key, new_right_ptr)
}

impl<K, V, const M: usize> LeafNode<K, V, M> {
    /// Constructs an empty leaf Node with no keys and no data.
    fn new() -> Self {
        Self {
            // SAFETY: An array of MaybeUninit doesn't need initialization.
            keys: unsafe { MaybeUninit::uninit().assume_init() },
            num_keys: 0,
            data: unsafe { MaybeUninit::uninit().assume_init() },
            next_in_layer: None,
        }
    }
    /// Moves the node into a Box and then immediately leaks the Box into a NonNull pointer.
    fn leak_from_box(self) -> NonNull<InnerOrLeafNode<K, V, M>> {
        let n: &mut InnerOrLeafNode<K, V, M> = Box::leak(Box::new(self)).into();
        NonNull::from(n)
    }
}

impl<K, V, const M: usize> InnerNode<K, V, M> {
    /// Constructs an empty inner Node with no keys and no children.
    fn new() -> Self {
        Self {
            // SAFETY: An array of MaybeUninit doesn't need initialization.
            keys: unsafe { MaybeUninit::uninit().assume_init() },
            num_keys: 0,
            children: unsafe { MaybeUninit::uninit().assume_init() },
            _data_marker: PhantomData,
        }
    }
    /// Moves the node into a Box and then immediately leaks the Box into a NonNull pointer.
    fn leak_from_box(self) -> NonNull<InnerOrLeafNode<K, V, M>> {
        let n: &mut InnerOrLeafNode<K, V, M> = Box::leak(Box::new(self)).into();
        NonNull::from(n)
    }
}

impl<K, V, const M: usize> InnerOrLeafNode<K, V, M> {
    /// SAFETY: Undefined behavior if this node is not a [LeafNode].
    unsafe fn as_leaf_node(&self) -> &LeafNode<K, V, M> {
        &*(self as *const Self as *const LeafNode<K, V, M>)
    }
    /// SAFETY: Undefined behavior if this node is not a [LeafNode].
    unsafe fn as_leaf_node_mut(&mut self) -> &mut LeafNode<K, V, M> {
        &mut *(self as *mut Self as *mut LeafNode<K, V, M>)
    }
    /// SAFETY: Undefined behavior if this node is not an [InnerNode].
    unsafe fn as_inner_node(&self) -> &InnerNode<K, V, M> {
        &*(self as *const Self as *const InnerNode<K, V, M>)
    }
    /// SAFETY: Undefined behavior if this node is not an [InnerNode].
    unsafe fn as_inner_node_mut(&mut self) -> &mut InnerNode<K, V, M> {
        &mut *(self as *mut Self as *mut InnerNode<K, V, M>)
    }
}

impl<'a, K, V, const M: usize> From<&'a mut LeafNode<K, V, M>>
    for &'a mut InnerOrLeafNode<K, V, M>
{
    fn from(x: &'a mut LeafNode<K, V, M>) -> Self {
        // SAFETY: In memory, an [InnerOrLeafNode] is a prefix of [LeafNode].
        unsafe { &mut *(x as *mut LeafNode<K, V, M> as *mut InnerOrLeafNode<K, V, M>) }
    }
}

impl<'a, K, V, const M: usize> From<&'a mut InnerNode<K, V, M>>
    for &'a mut InnerOrLeafNode<K, V, M>
{
    fn from(x: &'a mut InnerNode<K, V, M>) -> Self {
        // SAFETY: In memory, an [InnerOrLeafNode] is a prefix of [InnerNode].
        unsafe { &mut *(x as *mut InnerNode<K, V, M> as *mut InnerOrLeafNode<K, V, M>) }
    }
}

impl<K, V, const M: usize> InnerOrLeafNode<K, V, M> {
    /// Returns true if this node is a leaf node.
    fn is_leaf(height: usize) -> bool {
        height == 0
    }

    /// Returns an iterator over the keys of this node.
    fn keys(&self) -> Box<dyn Iterator<Item = &K> + '_> {
        Box::new(
            self.keys[0..self.num_keys]
                .iter()
                .map(|k| unsafe { k.assume_init_ref() }),
        )
    }

    /// Locates the given key in this node (not subtree).
    /// For a non-existent key, it returns the InChild value indicating where the key should be inserted.
    fn key_position<Q>(&self, key: &Q) -> KeyPosition
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        for (i, k) in self.keys().enumerate() {
            match k {
                k if k.borrow() > key => return KeyPosition::InChild(i),
                k if k.borrow() == key => return KeyPosition::Found(i),
                _ => {}
            }
        }
        KeyPosition::InChild(self.num_keys)
    }

    /// Returns true if the key is in the subtree starting from this node.
    /// SAFETY: The provided height must be correct.
    unsafe fn contains_key<Q>(&self, height: usize, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        match self.key_position(key) {
            KeyPosition::Found(_) => true,
            KeyPosition::InChild(i) => {
                if Self::is_leaf(height) {
                    return false;
                }
                self.as_inner_node().children[i]
                    .assume_init()
                    .as_ref()
                    .contains_key(height - 1, key)
            }
        }
    }

    /// Returns a reference to the value mapped to the given key or `None` if not present.
    /// SAFETY: The provided height must be correct.
    unsafe fn get<Q>(&self, height: usize, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if Self::is_leaf(height) {
            let leaf_node = self.as_leaf_node();
            return match self.key_position(key) {
                KeyPosition::Found(i) => Some(leaf_node.data[i].assume_init_ref()),
                KeyPosition::InChild(_) => None,
            };
        }
        match self.key_position(key) {
            KeyPosition::Found(i) | KeyPosition::InChild(i) => self.as_inner_node().children[i]
                .assume_init()
                .as_ref()
                .get(height - 1, key),
        }
    }

    /// Insert the given key into the subtree rooted at this node.
    /// Returns [InsertResult::Overfull] if the insertion makes this node overfull.
    /// In this case the node will have `M` keys and `M` children, with an
    /// additional right-most child in the returned enum.
    ///
    /// The caller must ensure that the returned node in `InsertResult::Overfull` is freed.
    /// SAFETY: The provided height must be correct.
    unsafe fn insert(&mut self, height: usize, key: K, value: V) -> InsertResult<K, V, M>
    where
        K: Ord + Clone,
    {
        // Find out where to insert the new key.
        let key_pos = match self.key_position(&key) {
            KeyPosition::Found(_) => return InsertResult::AlreadyPresent,
            KeyPosition::InChild(i) => i,
        };
        if Self::is_leaf(height) {
            insert_at(&mut self.as_leaf_node_mut().data, key_pos, value);
            insert_at(&mut self.keys, key_pos, key);
            self.num_keys += 1;
            if self.num_keys == M {
                return InsertResult::Overfull(None);
            }
            return InsertResult::Inserted;
        }
        // Not a leaf. Insert recursively.
        let inner_node = self.as_inner_node_mut();
        // SAFETY: An inner node always has a child to the right of each key.
        let left_child = inner_node.children[key_pos].assume_init().as_mut();
        let spillover_content = match left_child.insert(height - 1, key, value) {
            r @ InsertResult::Inserted | r @ InsertResult::AlreadyPresent => return r,
            InsertResult::Overfull(n) => n,
        };

        // Overfull. Need to split the child node.
        let (pulled_up_key, new_right_child) = split_insert(left_child, spillover_content);

        let spillover_node = insert_at(&mut inner_node.children, key_pos + 1, new_right_child);

        insert_at(&mut self.keys, key_pos, pulled_up_key);
        self.num_keys += 1;
        if self.num_keys == M {
            return InsertResult::Overfull(Some(spillover_node.assume_init()));
        }
        InsertResult::Inserted
    }
}

pub struct IntoIter<K, V, const M: usize> {
    _tree: BTree<K, V, M>,
    leaf_node: NodePtr<K, V, M>,
    key_index: usize,
}

impl<K, V, const M: usize> std::iter::IntoIterator for BTree<K, V, M> {
    type Item = K;
    type IntoIter = IntoIter<K, V, M>;
    fn into_iter(self) -> IntoIter<K, V, M> {
        let mut node = self.root;
        for _ in 0..self.height {
            let inner_node = unsafe { node.as_ref().as_inner_node() };
            node = unsafe { inner_node.children[0].assume_init() };
        }
        IntoIter {
            _tree: self,
            leaf_node: node,
            key_index: 0,
        }
    }
}

impl<K, V, const M: usize> Iterator for IntoIter<K, V, M> {
    type Item = K;
    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: self._tree keeps the tree alive including all nodes.
        let leaf_node = unsafe { self.leaf_node.as_mut().as_leaf_node_mut() };
        if self.key_index < leaf_node.num_keys {
            let key = unsafe {
                mem::replace(&mut leaf_node.keys[self.key_index], MaybeUninit::uninit())
                    .assume_init()
            };
            self.key_index += 1;
            return Some(key);
        }
        if let Some(next) = leaf_node.next_in_layer {
            self.leaf_node = next;
            self.key_index = 0;
            return self.next();
        }
        None
    }
}

impl<K, V, const M: usize> Drop for BTree<K, V, M> {
    fn drop(&mut self) {
        unsafe { drop_node(self.height, self.root) };
    }
}

unsafe fn drop_node<K, V, const M: usize>(height: usize, mut node: NodePtr<K, V, M>) {
    // Drop the node's keys.
    let node_mut = node.as_mut();
    for k in &mut node_mut.keys[0..node_mut.num_keys] {
        k.assume_init_drop();
    }
    if height == 0 {
        // Drop this leaf node's data.
        let leaf_node = node.as_mut().as_leaf_node_mut();
        for d in &mut leaf_node.data[0..leaf_node.num_keys] {
            d.assume_init_drop();
        }
        // Drop the node itself, casting it to the correct type.
        Box::from_raw(node.as_ptr() as *mut LeafNode<K, V, M>);
    } else {
        // Drop this inner node's children.
        let inner_node = node.as_ref().as_inner_node();
        for c in &inner_node.children[0..inner_node.num_keys + 1] {
            drop_node(height - 1, c.assume_init());
        }
        // Drop the node itself, casting it to the correct type.
        Box::from_raw(node.as_ptr() as *mut InnerNode<K, V, M>);
    }
}

impl<K, V, const M: usize> Default for BTree<K, V, M> {
    fn default() -> Self {
        BTree::new()
    }
}

impl<K, V, const M: usize> BTree<K, V, M> {
    /// Returns a new empty BTree.
    pub fn new() -> BTree<K, V, M> {
        BTree {
            root: LeafNode::new().leak_from_box(),
            height: 0,
        }
    }

    /// Returns an immutable reference to the root node.
    fn root_as_ref(&self) -> &InnerOrLeafNode<K, V, M> {
        // SAFETY: The root is always a valid pointer.
        unsafe { self.root.as_ref() }
    }

    /// Returns true if the key is in the tree.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        // SAFETY: self.height is the correct height of the root node.
        unsafe { self.root_as_ref().contains_key(self.height, key) }
    }

    /// Returns a reference to the value mapped to the given key or `None` if not present.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        // SAFETY: self.height is the correct height of the root node.
        unsafe { self.root_as_ref().get(self.height, key) }
    }

    /// Inserts the key into the tree.
    pub fn insert(&mut self, key: K, value: V)
    where
        K: Clone + Ord,
    {
        unsafe {
            let height = self.height;
            let spillover_node = match self.root.as_mut().insert(height, key, value) {
                InsertResult::Inserted | InsertResult::AlreadyPresent => return,
                InsertResult::Overfull(node) => node,
            };
            // Split the root and put both parts under a new root.
            let (pulled_up_key, new_right_child) = split_insert(self.root.as_mut(), spillover_node);
            let old_root = std::mem::replace(&mut self.root, InnerNode::new().leak_from_box());
            let r = self.root.as_mut().as_inner_node_mut();
            r.children[0].write(old_root);
            r.children[1].write(new_right_child);
            r.keys[0].write(pulled_up_key);
            r.num_keys = 1;

            self.height += 1;
        }
    }
}
