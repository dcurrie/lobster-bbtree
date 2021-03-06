# Lobster BBTree API

Bounded Balance Trees a.k.a. Weight Balanced Trees

a persistent data structure providing a generic (parameterized) key,value map
 * Insert (``add``), lookup (``get``), and delete (``del``) in O(log(N)) time
 * Key-ordered iterators (``inorder`` and ``revorder``)
 * Lookup by relative position from beginning or end (``getNth``) in O(log(N) time
 * Get the position (``rank``) by key in O(log(N)) time
 * Efficient set operations using tree keys
 * Map extensions to set operations with optional value merge control for duplicates

#### Type

```
class BBTree<K,V>: // BBTree is a generic type with keys and values of types K and V
    left:  BBTree<K,V>? // left subtree; may be nil
    right: BBTree<K,V>? // right subtree; may be nil
    size:  int          // the size of the (sub-)tree rooted in this node
    key:   K            // the search key; must support the generic cmp function
    val:   V            // the data value associated with the key
```

Note that `BBTree<K,V>` is intended to be an immutable opaque data structure.

#### Functions

| Basic Functions for *key,value* mapping and inquiry |
|:---------------------|
| **add**(root: BBTree<K,V>, key: K, value: V) -> BBTree<K,V> |
| Returns a new tree with the (`key`, `value`) pair added, or replaced if `key` is already in the tree `root`. O(log N) |
| **del**(root: BBTree<K,V>, key: K) -> BBTree<K,V> |
| Deletes `key` from tree `root`. Does nothing if the key does not exist. O(log N) |
| **delMax**(root: BBTree<K,V>) -> BBTree<K,V> |
| Delete the maximum element from tree `root`. O(log N) |
| **delMin**(root: BBTree<K,V>) -> BBTree<K,V> |
| Delete the minimum element from tree `root`. O(log N) |
| **get**(root: BBTree<K,V>, key: K, vdefault: V) -> V |
| Retrieves the value for `key` in the tree `root` iff `key` is in the tree.  Otherwise, `vdefault` is returned. O(log N) |
| **getMax**(root: BBTree<K,V>, kdefault K, vdefault V) -> K, V |
| Retrieves the key,value pair with the largest key in the tree `root`. For an empty tree `kdefault, vdefault` is returned. O(log N) |
| **getMin**(root: BBTree<K,V>, kdefault: K, vdefault: V) ->  K, V |
| Retrieves the key,value pair with the smallest key in the tree `root`. For an empty tree `kdefault, vdefault` is returned. O(log N) |
| **getNth**(root: BBTree<K,V>, index: int, kdefault: K, vdefault: V) -> K, V |
| Get the key,value pair of the 0-based `index` key in the tree `root` when index is positive and less than the tree length. Or get the tree length plus `index` key in the tree `root` when the `index` is negative and greater than the negative tree length. Otherwise, `kdefault, vdefault` is returned. O(log N) |
|**getNext**(root: BBTree<K,V>, key K, kdefault K, vdefault V) -> K, V |
| Returns the key,value pair with smallest key > `key`. It is almost inorder successor, but it also works when `key` is not present. If there is no such successor key in the tree, `kdefault, vdefault` is returned. O(log N) |
|**getPrev**(root: BBTree<K,V>, key K, kdefault K, vdefault: V) -> K, V |
| Returns the key,value pair with largest key < `key`. It is almost inorder predecessor, but it also works when `key` is not present. If there is no such predecessor key in the tree, `kdefault, vdefault` is returned. O(log N) |
| **len**(root: BBTree<K,V>) -> int |
| Returns the number of keys in tree at `root`.  O(1) |
| **rank**(root: BBTree<K,V>, key: K, rdefault: int) -> int |
| Retrieves the 0-based index of `key` in the tree `root` iff `key` is in the tree. Otherwise, `rdefault` is returned. O(log N) |

| HOF |
|:---------------------|
| **foldl**(root: BBTree<K,V>, base: T, f: (K,V,T)->T)) -> T |
| Applies the function `f` to each key value pair of tree `root` in order (left ro right). Uses the `base` value for the first leftmost operand. So, for example, to construct a sum of the tree values, you could use ``foldl(root, 0): _a; _b + _c`` and this will print the keys in order prefixed by "keys:" and separated by ":": `print(foldl(tree, "keys") k, v, b: v; concat_string([b, k],":"))` |
| **foldr**(root: BBTree<K,V>, base: T, f: (K,V,T)->T)) -> T |
| Applies the function `f` to each key value pair of tree `root` in reverse order (right to left). Uses the `base` value for the first rightmost operand. |
| **foreach**(root: BBTree<K,V>, f: (K,V)->void) -> void |
| Applies function `f` to each key and corresponding value of `root`, discarding the results. |
| **map**(root: BBTree<K,V>, f: (K,V,T)->T) -> BBTree<K,T> |
| Returns a new tree with the keys of tree `root` and values that are the result of applying `f` to each key and corresponding value in `root`. |

| Set operation functions on *key,value* maps |
|:---------------------|
| **contains**(root: BBTree<K,V>, key: K) -> bool |
| Returns `true` if `key` is in the tree `root` otherwise `false`. O(log N) |
| **union**(tree1: BBTree<K,V>, tree2: BBTree<K,V>) -> BBTree<K,V> |
| Returns the union of the sets represented by the keys in `tree1` and `tree2`.  When viewed as maps, returns the key,value pairs that appear in either tree; if a key appears in both trees, the value for that key is selected from `tree1`, so this function is asymmetrical for maps. If you need more comtrol over how the values are selected for duplicate keys, see `unionMerge`. O(M + N) but if the minimum key of one tree is greater than the maximum key of the other tree then O(log M) where M is the size of the larger tree. |
| **unionMerge**(tree1: BBTree<K,V>, tree2: BBTree<K,V>, merge: (K,V,V)->V) -> BBTree<K,V> |
| Returns the union of the sets represented by the keys in `tree1` and `tree2`. When viewed as maps, returns the key,value pairs that appear in either tree; if a key appears in both trees, the value for that key is the result of the supplied `merge` function, which is passed the common key, and the values from `tree1` and `tree2` respectively. O(M + N) but if the minimum key of one tree is greater than the maximum key of the other tree then O(log M) where M is the size of the larger tree. |
| **intersection**(tree1: BBTree<K,V>, tree2: BBTree<K,V>) -> BBTree<K,V> |
| Returns the set intersection of `tree1` and `tree2`. In other words, returns the keys that are in both trees. When viewed as maps, returns the key,value pairs for keys that appear in both trees; the value each key is selected from `tree1`, so this function is asymmetrical for maps. If you need more comtrol over how the values are selected for duplicate keys, see `intersectionMerge`. O(M + N) |
| **intersectionMerge**(tree1: BBTree<K,V>, tree2: BBTree<K,V>, merge: (K,V,V)->V) -> BBTree<K,V> |
| Returns the set intersection of `tree1` and `tree2`. In other words, returns the keys that are in both trees. When viewed as maps, returns the key,value pairs for keys that appear in both trees; the value for each key is the result of the supplied `merge` function, which is passed the common key, and the values from `tree1` and `tree2` respectively.  O(M + N) |
| **difference**(tree1: BBTree<K,V>, tree2: BBTree<K,V>) -> BBTree<K,V> |
| Returns the asymmetric set difference between `tree1` and `tree2`. In other words, returns the keys that are in `tree1`, but not in `tree2`. O(M + N) |
| **symmetricDifference**(tree1: BBTree<K,V>, tree2: BBTree<K,V>) -> BBTree<K,V> |
| Returns the symmetric set difference between `tree1` and `tree2`. In other words, returns the keys that are in `tree1`, but not in `tree2`, union the keys that are in `tree2` but not in `tree1`.  O(M + N) |
| **isSubset**(tree1: BBTree<K,V>, tree2: BBTree<K,V>) -> bool |
| Returns true iff the keys in `tree1` form a subset of the keys in `tree2`. In other words, if all the keys that are in `tree1` are also in `tree2`. O(N) where N is `len(tree1)`. Use `isProperSubset` instead to determins that there are keys in `tree2` that are not in `tree1`. |
| **isProperSubset**(tree1: BBTree<K,V>, tree2: BBTree<K,V>) -> bool |
| Returns true iff the keys in `tree1` form a proper subset of the keys in `tree2`. In other words, if all the keys that are in `tree1` are also in `tree2`, but there are keys in `tree2` that are not in `tree1`.  O(N) where N is `len(tree1)` |
| **setEqual**(tree1: BBTree<K,V>, tree2: BBTree<K,V>) -> bool |
| Returns true if both `tree1` and `tree2` have the same keys. O(N) where N is `len(tree1)` |
| **disjoint**(tree1: BBTree<K,V>, tree2: BBTree<K,V>) -> bool |
| Returns true iff `tree1` and `tree2` have no keys in common. O(N) where N is `len(tree1)` |
| **toSet**(keys: [K]) -> BBTree<K,bool> |
| Creates a BBTree set that contains the given `keys` with value `true`. |
