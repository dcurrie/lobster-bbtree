/*
Copyright (c) 2012-19 Doug Currie, Londonderry, NH, USA

Permission is hereby granted, free of charge, to any person obtaining a copy of this software 
and associated documentation files (the "Software"), to deal in the Software without 
restriction, including without limitation the rights to use, copy, modify, merge, publish, 
distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the 
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or 
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING 
BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND 
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, 
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, 
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

/* Bounded Balance Trees a.k.a. Weight Balanced Trees

References:

Implementing Sets Efficiently in a Functional Language
Stephen Adams
CSTR 92-10
Department of Electronics and Computer Science University of Southampton Southampton S09 5NH

Adams’ Trees Revisited Correct and Efficient Implementation
Milan Straka <fox@ucw.cz>
Department of Applied Mathematics Charles University in Prague, Czech Republic
*/

// Bounded Balance Trees a.k.a. Weight Balanced Trees
// 
// a persistent data structure providing a generic (parameterized) key,value map
//
// * Insert (``add``), lookup (``get``), and delete (``del``) in O(log(N)) time
// * Key-ordered iterators (``inorder`` and ``revorder``)
// * Lookup by relative position from beginning or end (``getNth``) in O(log(N)) time
// * Get the position (``rank``) by key in O(log(N)) time
// * Efficient set operations using tree keys
// * Map extensions to set operations with optional value merge control for duplicates

/* 
class BBTree<K,V>: // BBTree is a generic type with keys and values of types K and V
    left:  BBTree?     // left subtree; may be nil
    right: BBTree?     // right subtree; may be nil
    size:  int         // the size of the (sub-)tree rooted in this node
    key:   K           // the search key; must support the generic ``cmp`` proc
    val:   V           // the data value associated with the key, and stored in a node
*/
// /*
class BBTree: // BBTree is a generic type with keys and values of types K and V
    left:  BBTree?     // left subtree; may be nil
    right: BBTree?     // right subtree; may be nil
    size:  int         // the size of the (sub-)tree rooted in this node
    key:   string      // the search key; must support the generic ``cmp`` proc
    val:   int         // the data value associated with the key, and stored in a node
// */

def cmp(x:int,   y:int)   -> int: return x - y

def cmp(x:float, y:float) -> int:
    if x < y:
        return -1
    else: if x > y:
        return 1
    else:
        return 0

def cmp(x:string, y:string) -> int:
    if x < y:
        return -1
    else: if x > y:
        return 1
    else:
        return 0

enum balance_criteria: // balance criteria
    omega = 3
    alpha = 2

def nodeSize(n:BBTree?) -> int: // n: BBTree[K,V]
//def nodeSize(n) -> int: // n: BBTree<K,V>?
    if not n:
        return 0
    else:
        return n.size

def len(root) -> int:
    // Returns the number of keys in tree at `root`.  O(1)
    return nodeSize(root)

def newLeaf(key, value): // -> BBTree<K,V>
    // constructor for a leaf node
    return BBTree { left: nil, right: nil, size: 1, key: key, val: value }

def newNode(left, key, value, right): // -> BBTree<K,V>
    // constructor for a new node
    let size = nodeSize(left) + 1 + nodeSize(right)
    return BBTree { left: left, right: right, size: size, key: key, val: value }

/* **************************** balance ********************************
//
singleL l k (Node rl _ rk rr) = node (node l k rl) rk rr
singleR (Node ll _ lk lr) k r = node ll lk (node lr k r)
doubleL l k (Node (Node rll _ rlk rlr) _ rk rr) =
  node (node l k rll) rlk (node rlr rk rr)
doubleR (Node ll _ lk (Node lrl _ lrk lrr)) k r =
  node (node ll lk lrl) lrk (node lrr k r)

balance left key right
    | size left + size right <= 1 = node left key right
    | size right > omega * size left + delta = case right of
         (Node rl _ _ rr) | size rl<alpha*size rr -> singleL left key right
                          | otherwise             -> doubleL left key right
    | size left > omega * size right + delta = case left of
         (Node ll _ _ lr) | size lr<alpha*size ll -> singleR left key right
                          | otherwise             -> doubleR left key right
    | otherwise = node left key right
*/

def singleL(left, key, value, right): // -> BBTree<K,V>
    return newNode(newNode(left, key, value, right.left),
                        right.key, 
                        right.val, 
                        right.right)

def doubleL(left, key, value, right): // -> BBTree<K,V>
    let rl = right.left
    assert rl
    return newNode(newNode(left, key, value, rl.left),
                     rl.key, 
                     rl.val, 
                     newNode(rl.right, right.key, right.val, right.right))


def singleR(left, key, value, right): // -> BBTree<K,V>
    return newNode(left.left,
                     left.key,
                     left.val,
                     newNode(left.right, key, value, right))

def doubleR(left, key, value, right): // -> BBTree<K,V>
    let lr = left.right
    assert lr
    return newNode(newNode(left.left, left.key, left.val, lr.left),
                     lr.key,
                     lr.val,
                     newNode(lr.right, key, value, right))

def balance(left, key, value, right): // -> BBTree<K,V>
    let sl = nodeSize(left)
    let sr = nodeSize(right)

    if ((sl + sr) <= 1):
        return newNode(left, key, value, right)
    else: if (sr > (omega * sl)):
        assert right
        if (nodeSize(right.left) < (alpha * nodeSize(right.right))):
            return singleL(left, key, value, right)
        else:
            return doubleL(left, key, value, right)
    else: if (sl > (omega * sr)):
        assert left
        if (nodeSize(left.right) < (alpha * nodeSize(left.left))):
            return singleR(left, key, value, right)
        else:
            return doubleR(left, key, value, right)
    else:
        return newNode(left, key, value, right)

/* **************************** insert ********************************
#
insert :: Ord a => a -> BBTree a -> BBTree a
insert k Nil = node Nil k Nil
insert k (Node left _ key right) = case k ‘compare‘ key of
                                     LT -> balance (insert k left) key right
                                     EQ -> node left k right
                                     GT -> balance left key (insert k right)
*/

def add(root, key, value): // -> BBTree<K,V>
    // Returns a new tree with the (`key`, `value`) pair added, or replaced if `key` is already
    // in the tree `root`. O(log N)
    if root: // root != nil:
        let dif = cmp(key, root.key)
        if (dif < 0):
            return balance(add(root.left, key, value), root.key, root.val, root.right)
        else: if (dif > 0):
            return balance(root.left, root.key, root.val, add(root.right, key, value))
        else: // key and root.key are equal
            //if (value == root.val)
            //    // no need to allocate a new node
            //    return node
            //else:
            return newNode(root.left, key, value, root.right)
    else:
        return newLeaf(key, value)
//
// attempt to make gerneric version work,
// which fails add(nil, str, int) cuz no type for root.key in cmp()
// this version fails with: "=" (right argument) requires type: BBTree?, got: BBTree_s_i
//
//    if not root:
//        root = newLeaf(key, value)
//        return root
//    else:
//        let dif = cmp(key, root.key)
//        if (dif < 0):
//            return balance(add(root.left, key, value), root.key, root.val, root.right)
//        else: if (dif > 0):
//            return balance(root.left, root.key, root.val, add(root.right, key, value))
//        else: // key and root.key are equal
//            //if (value == root.val)
//            //    // no need to allocate a new node
//            //    return node
//            //else:
//            return newNode(root.left, key, value, root.right)

/* ***************************** lookup *********************************
*/

def get(root, key, vdefault): // -> V
    // Retrieves the value for `key` in the tree `root` iff `key` is in the tree. 
    // Otherwise, `vdefault` is returned. O(log N)
    var node = root
    while node:
        let dif = cmp(key, node.key)
        if dif < 0:
            if node.left: node = node.left else: return vdefault
        else: if dif > 0:
            if node.right: node = node.right else: return vdefault
        else: // key and node.key are eq
            return node.val
    return vdefault

def getNth(root, index: int, kdefault, vdefault): // -> K, V
    // Get the key,value pair of the 0-based `index` key in the tree `root` when index is 
    // positive and less than the tree length. Or get the tree length plus `index` key in 
    // the tree `root` when the `index` is negative and greater than the negative tree length.
    // Otherwise, `kdefault, vdefault` is returned. O(log N)
    let treesize = nodeSize(root)
    var uindex = 0
    if (index < treesize) and (index >= (-treesize)):
        if index < 0:
            uindex = treesize + index // when negative, reverse index from end rather than inorder
        else:
            uindex = index // all set
        var node = root
        while node:
            let leftsize = nodeSize(node.left)
            if uindex < leftsize and node.left:
                node = node.left
            else: if uindex > leftsize and node.right:
                uindex -= (leftsize + 1)
                node = node.right
            else: // we are there!
                return node.key, node.val
    // else index is out of range; default is returned
    return kdefault, vdefault

def getMin(root, kdefault, vdefault): // ->  K, V
    // Retrieves the key,value pair with the smallest key in the tree `root`
    // For an empty tree `kdefault, vdefault` is returned. O(log N)
    if root:
        var node = root
        while node.left:
            node = node.left
        return node.key, node.val
    else:
        return kdefault, vdefault

def getMax(root, kdefault, vdefault): // -> K, V
    // Retrieves the key,value pair with the largest key in the tree `root`
    // For an empty tree `kdefault, vdefault` is returned. O(log N)
    if root:
        var node = root
        while node.right:
            node = node.right
        return node.key, node.val
    else:
        return kdefault, vdefault

def getKV(node, kdefault, vdefault): // -> K, V
    if node:
        return node.key, node.val
    else:
        return kdefault, vdefault

def getNext(root, key, kdefault, vdefault): // -> K, V
    // Returns the key,value pair with smallest key > `key`.
    // It is almost inorder successor, but it also works when `key` is not present.
    // If there is no such successor key in the tree, `kdefault, vdefault` is returned. O(log N)
    var last_left_from = nil
    var node = root
    while 1:
        if not node:
            return getKV(last_left_from, kdefault, vdefault) // key not found
        else:
            let dif = cmp(key, node.key)
            if (dif < 0):
                last_left_from = node
                node = node.left
            else: if (dif > 0):
                node = node.right
            else: // key and node.key are eq
                // return value from min node of right subtree, or from last_left_from if none
                if node.right:
                    return getMin(node.right, kdefault, vdefault)
                else:
                    return getKV(last_left_from, kdefault, vdefault)

def getPrev(root, key, kdefault, vdefault): // -> KV<K,V>
    // Returns the key,value pair with largest key < `key`.
    // It is almost inorder predecessor, but it also works when `key` is not present.
    // If there is no such predecessor key in the tree, `kdefault, vdefault` is returned. O(log N)
    var last_right_from = nil
    var node = root
    while 1:
        if not node:
            return getKV(last_right_from, kdefault, vdefault) // key not found
        else:
            let dif = cmp(key, node.key)
            if (dif < 0):
                node = node.left
            else: if (dif > 0):
                last_right_from = node
                node = node.right
            else: // key and node.key are eq
                // return value from max node of left subtree, or from last_right_from if none
                if node.left:
                    return getMax(node.left, kdefault, vdefault)
                else:
                    return getKV(last_right_from, kdefault, vdefault)

/* ***************************** delete *********************************
#
delete :: Ord a => a -> BBTree a -> BBTree a
delete _ Nil = Nil
delete k (Node left _ key right) = case k ‘compare‘ key of
                                     LT -> balance (delete k left) key right
                                     EQ -> glue left right
                                     GT -> balance left key (delete k right)
  where glue Nil right = right
        glue left Nil = left
        glue left right
          | size left > size right = let (key’, left’) = extractMax left
                                     in node left’ key’ right
          | otherwise              = let (key’, right’) = extractMin right
                                     in node left key’ right’
        extractMin (Node Nil _ key right) = (key, right)
        extractMin (Node left _ key right) = case extractMin left of
          (min, left’) -> (min, balance left’ key right)
        extractMax (Node left _ key Nil) = (key, left)
        extractMax (Node left _ key right) = case extractMax right of
          (max, right’) -> (max, balance left key right’)
*/

//def extractMin(node:BBTree): // -> mink, minv, node' : K, V, BBTree[K,V]
//    if node.left:
//        let mink, minv, nodep = extractMin(node.left)
//        return mink, minv, balance(nodep, node.key, node.val, node.right)
//    else: return node.key, node.val, node.right
def extractMin(node:BBTree): // -> mink, minv, node' : K, V, BBTree[K,V]
    if not node.left:
        return node.key, node.val, node.right
    else: 
        let mink, minv, nodep = extractMin(node.left)
        return mink, minv, balance(nodep, node.key, node.val, node.right)

//def extractMax(node:BBTree): // -> maxk, maxv, node' : K, V, BBTree[K,V]
//    if node.right:
//        let maxk, maxv, nodep = extractMax(node.right)
//        return maxk, maxv, balance(node.left, node.key, node.val, nodep)
//    else: return node.key, node.val, node.left
def extractMax(node:BBTree): // -> maxk, maxv, node' : K, V, BBTree[K,V]
    if not node.right:
        return node.key, node.val, node.left
    else: 
        let maxk, maxv, nodep = extractMax(node.right)
        return maxk, maxv, balance(node.left, node.key, node.val, nodep)

def glue(left, right): // -> BBTree<K,V>
    if not left:
        return right
    else: if not right:
        return left
    else: if nodeSize(left) > nodeSize(right):
        let maxk, maxv, leftp = extractMax(left)
        return newNode(leftp, maxk, maxv, right)
    else:
        let mink, minv, rightp = extractMin(right)
        return newNode(left, mink, minv, rightp)

def del(root, key): // -> BBTree<K,V>
    // Deletes `key` from tree `root`. Does nothing if the key does not exist.
    // O(log N)
    if root:
        let dif = cmp(key, root.key)
        if (dif < 0):
            return balance(del(root.left, key), root.key, root.val, root.right)
        else: if (dif > 0):
            return balance(root.left, root.key, root.val, del(root.right, key))
        else: // key and root.key are eq
            return glue(root.left, root.right)
    else:
        return root

def delMin(root): // -> BBTree<K,V>
    // Delete the minimum element from tree `root`. O(log N)
    if not root:
        return root
    else:
        let mink, minv, node = extractMin(root)
        // discard mink
        // discard minv
        return node

def delMax(root): // -> BBTree<K,V>
    // Delete the maximum element from tree `root`. O(log N)
    if not root:
        return root
    else:
        let maxk, maxv, node = extractMax(root)
        // discard maxk
        // discard maxv
        return node

/* ****************************** rank ***********************************
*/

def rank(root, key, rdefault: int) -> int:
    // Retrieves the 0-based index of `key` in the tree `root` iff `key` is in the tree. 
    // Otherwise, `rdefault` is returned. O(log N)
    var result = rdefault
    var n = 0
    var node = root
    while node:
        let dif = cmp(key, node.key)
        if (dif < 0):
            node = node.left
        else: if (dif > 0):
            n += 1 + nodeSize(node.left)
            node = node.right
        else: // key and node.key are eq
            result = n + nodeSize(node.left)
            node = nil // break
    return result

/* **************************** fold & map ********************************
*/

def foldr(root, base, f): // -> T // base: T, f: (K,V,T)->T,
    // Applies the function `f` to each key value pair of tree `root` in reverse order (right to left).
    // Uses the `base` value for the first rightmost operand. So, for example TODO
    // Uses explicit stack.
    var result = base
    let stack = [] // : [BBTree<K,V>]
    var curr = root
    while curr or length(stack) > 0:
        while (curr):
            push(stack, curr) // push node before going right
            curr = curr.right
        // at the rightmost node; curr is == tos
        curr = pop(stack)
        result = f(curr.key, curr.val, result)
        curr = curr.left // now go left
    return result

def foldl(root, base, f): // -> T // base: T, f: (K,V,T)->T,
    // Applies the function `f` to each key value pair of tree `root` in order (left ro right).
    // Uses the `base` value for the first leftmost operand. So, for example, to construct a
    // sum of the tree values, you could use ``foldl(root, 0): _a; _b + _c`` and this will print
    // the  keys in order prefixed by "keys:" and separated by ":":
    //    print(foldl(tree, "keys") k, v, b: v; concat_string([b, k],":"))
    // Uses explicit stack.
    var result = base
    let stack = [] // : [BBTree<K,V>]
    var curr = root
    while curr or length(stack) > 0:
        while (curr):
            push(stack, curr) // push node before going left
            curr = curr.left
        // at the leftmost node; curr is == tos
        curr = pop(stack)
        result = f(curr.key, curr.val, result)
        curr = curr.right // now go right
    return result

def foreach(root, f): // -> void // root: BBTree<K,V>, f: (K,V)->void
    // Applies function `f` to each key and corresponding value of `root`, discarding
    // the results.
    foldl(root, false): f(_k,_v);false

def map(root, f): // -> BBTree<K,T> // base: T, f: (K,V,T)->T,
    // Returns a new tree with the keys of tree `root` and values that are the result of 
    // applying `f` to each key and corresponding value. So, for example, TODO
    //
    // to construct a
    // tree with values replaced by concatenated string of key,value pairs, you could use
    // 
    // .. code-block::
    // 
    //     map(root, proc (k: int, v: int): string = $k & ":" & $v)
    if root:
        return newNode(map(root.left, f), root.key, f(root.key, root.val), map(root.right, f))
    else:
        return root

/* **************************** set operations ********************************
*/

// This is Adams's concat3
//
def join(key, val, left, right): // -> BBTree<K,V>
    if not left:
        return add(right, key, val)
    else: if not right:
        return add(left, key, val)
    else:
        let sl = nodeSize(left)
        let sr = nodeSize(right)
        if (omega * sl) < sr:
            return balance(join(key, val, left, right.left), right.key, right.val, right.right)
        else: if (omega * sr) < sl:
            return balance(left.left, left.key, left.val, join(key, val, left.right, right))
        else:
            return newNode(left, key, val, right)

// This is Adams's concat
//
def join(left, right): // -> BBTree<K,V>
    if not left:
        return right
    else: if not right:
        return left
    else:
        let key, val, rightp = extractMin(right)
        return join(key, val, left, rightp)

// This is Adams's split_lt and split_gt combined into one function, along with contains(root, key)
//
def splitLtGt(key, root): // -> (BBTree[K,V], bool, BBTree[K,V])
    if not root:
        return root, false, root
    else:
        let dif = cmp(key, root.key)
        if dif < 0:
            let l, b, r = splitLtGt(key, root.left)
            return l, b, join(root.key, root.val, r, root.right)
        else: if dif > 0:
            let l, b, r = splitLtGt(key, root.right)
            return join(root.key, root.val, root.left, l), b, r
        else: // key and node.key are eq
            return root.left, true, root.right

def splitMerge(key, val, root, merge): // merge: proc (k, v1, v2)
    // -> (BBTree[K,V], bool, V, BBTree[K,V]) =
    if not root:
        return root, false, val, root
    else:
        let dif = cmp(key, root.key)
        if dif < 0:
            let l, b, v, r = splitMerge(key, val, root.left, merge)
            return l, b, v, join(root.key, root.val, r, root.right)
        else: if dif > 0:
            let l, b, v, r = splitMerge(key, val, root.right, merge)
            return join(root.key, root.val, root.left, l), b, v, r
        else: // key and node.key are eq
            return root.left, true, merge(key, val, root.val), root.right

def union(tree1, tree2): // -> BBTree<K,V>
    // Returns the union of the sets represented by the keys in `tree1` and `tree2`.
    // When viewed as maps, returns the key,value pairs that appear in either tree; if
    // a key appears in both trees, the value for that key is selected from `tree1`, so
    // this function is asymmetrical for maps. If you need more comtrol over how the 
    // values are selected for duplicate keys, see `unionMerge`. O(M + N) but if the minimum
    // key of one tree is greater than the maximum key of the other tree then O(log M) 
    // where M is the size of the larger tree.
    if not tree1:
        return tree2
    else: if not tree2:
        return tree1
    else:
        let l, b, r = splitLtGt(tree1.key, tree2)
        // discard b
        return join(tree1.key, tree1.val, union(tree1.left, l), union(tree1.right, r))

def unionMerge(tree1, tree2, merge): // merge: (K,V,V)->V // -> BBTree<K,V>
    // Returns the union of the sets represented by the keys in `tree1` and `tree2`.
    // When viewed as maps, returns the key,value pairs that appear in either tree; if
    // a key appears in both trees, the value for that key is the result of the supplied
    // `merge` function, which is passed the common key, and the values from `tree1` and 
    // `tree2` respectively.  O(M + N) but if the minimum
    // key of one tree is greater than the maximum key of the other tree then O(log M) 
    // where M is the size of the larger tree.
    if not tree1:
        return tree2
    else: if not tree2:
        return tree1
    else:
        let l, b, v, r = splitMerge(tree1.key, tree1.val, tree2, merge)
        // discard b
        return join(tree1.key, v, unionMerge(tree1.left, l, merge), unionMerge(tree1.right, r, merge))

def difference(tree1, tree2): // -> BBTree<K,V>
    // Returns the asymmetric set difference between `tree1` and `tree2`. In other words, 
    // returns the keys that are in `tree1`, but not in `tree2`.  O(M + N)
    if not tree1 or not tree2:
        return tree1
    else:
        let l, b, r = splitLtGt(tree2.key, tree1)
        // discard b
        return join(difference(l, tree2.left), difference(r, tree2.right))

def symmetricDifference(tree1, tree2): // -> BBTree<K,V>
    // Returns the symmetric set difference between `tree1` and `tree2`. In other words, 
    // returns the keys that are in `tree1`, but not in `tree2`, union the keys that are in 
    // `tree2` but not in `tree1`.  O(M + N)
    if not tree1:
        return tree2
    else: if not tree2:
        return tree1
    else:
        let l, b, r = splitLtGt(tree2.key, tree1)
        if b:
            return join(symmetricDifference(l, tree2.left), symmetricDifference(r, tree2.right))
        else:
            return join(tree2.key, tree2.val, symmetricDifference(l, tree2.left), symmetricDifference(r, tree2.right))

def contains(root, key): // -> bool
    // Returns `true` if the `key` is in the tree `root`
    // otherwise `false`. O(log N)
    var node:BBTree? = root // why is type annotation needed to prevent (1) below? 
    while node:
        let dif = cmp(key, node.key)
        if dif < 0:
            node = node.left // (1) error: "=" (right argument) requires type: BBTree, got: BBTree?
        else: if dif > 0:
            assert(node) // why is this necessary after `while` test!?
            node = node.right
        else: // key and node.key are eq
            return true
    return false

def intersection(tree1, tree2): // -> BBTree<K,V>
    // Returns the set intersection of `tree1` and `tree2`. In other words, returns the keys
    // that are in both trees. 
    // When viewed as maps, returns the key,value pairs for keys that appear in both trees; 
    // the value each key is selected from `tree1`, so
    // this function is asymmetrical for maps. If you need more comtrol over how the 
    // values are selected for duplicate keys, see `intersectionMerge`. O(M + N)
    if not tree1:
        return tree1
    else: if not tree2:
        return tree2
    else:
        let l, b, r = splitLtGt(tree1.key, tree2)
        if b:
            return join(tree1.key, tree1.val, intersection(tree1.left, l), intersection(tree1.right, r))
        else:
            return join(intersection(tree1.left, l), intersection(tree1.right, r))

def intersectionMerge(tree1, tree2, merge): // merge: (K,V,V)->V // -> BBTree<K,V>
    // Returns the set intersection of `tree1` and `tree2`. In other words, returns the keys
    // that are in both trees. 
    // When viewed as maps, returns the key,value pairs for keys that appear in both trees; 
    // the value for each key is the result of the supplied
    // `merge` function, which is passed the common key, and the values from `tree1` and 
    // `tree2` respectively.  O(M + N)
    if not tree1:
        return tree1
    else: if not tree2:
        return tree2
    else:
        let l, b, v, r = splitMerge(tree1.key, tree1.val, tree2, merge)
        if b:
            return join(tree1.key, v, intersectionMerge(tree1.left, l, merge), intersectionMerge(tree1.right, r, merge))
        else:
            return join(intersectionMerge(tree1.left, l, merge), intersectionMerge(tree1.right, r, merge))

def isSubset(tree1, tree2): // -> bool
    // Returns true iff the keys in `tree1` form a subset of the keys in `tree2`. In other words, 
    // if all the keys that are in `tree1` are also in `tree2`. O(N) where N is `len(tree1)`
    // Use `isProperSubset` instead to determins that there are keys in `tree2` that are not in `tree1`.
    if not tree1:
        return true
    else: if len(tree1) > len(tree2):
        return false
    else:
        assert(tree2) // tree2 is not nil or else the above length test would have been true
        let dif = cmp(tree1.key, tree2.key)
        if dif < 0:
            return isSubset(tree1.left, tree2.left) and
                     tree2.contains(tree1.key) and
                     isSubset(tree1.right, tree2)
        else: if dif > 0:
            return isSubset(tree1.right, tree2.right) and
                     tree2.contains(tree1.key) and 
                     isSubset(tree1.left, tree2)
        else: // tree1.key and tree2.key are eq
            return isSubset(tree1.left, tree2.left) and isSubset(tree1.right, tree2.right)

def disjoint(tree1, tree2): // -> bool
    // Returns true iff `tree1` and `tree2` have no keys in common. O(N) where N is
    // `len(tree1)`
    if tree1 and tree2:
        let dif = cmp(tree1.key, tree2.key)
        if dif < 0:
            if not disjoint(tree1.left, tree2.left): return false
            if tree2.contains(tree1.key): return false
            return disjoint(tree1.right, tree2)
        else: if dif > 0:
            if not disjoint(tree1.right, tree2.right): return false
            if tree2.contains(tree1.key): return false 
            return disjoint(tree1.left, tree2)
        else: // tree1.key and tree2.key are eq
            return false
    else: // tree1 or tree2 is empty
        return true // default

def isProperSubset(tree1, tree2): // -> bool
    // Returns true iff the keys in `tree1` form a proper subset of the keys in `tree2`. 
    // In other words, if all the keys that are in `tree1` are also in `tree2`, but there are 
    // keys in `tree2` that are not in `tree1`.  O(N) where N is `len(tree1)`
    return isSubset(tree1, tree2) and len(tree1) < len(tree2)

def setEqual(tree1, tree2): // -> bool
    // Returns true if both `tree1` and `tree2` have the same keys.
    return len(tree1) == len(tree2) and isSubset(tree1, tree2)

// def `+`(s1, s2): // -> BBTree[K,V]
//     // Alias for `union(s1, s2) <#union,BBTree[K,V],BBTree[K,V]>`_.
//     return union(s1, s2)
// 
// def `*`(s1, s2): // -> BBTree[K,V]
//     // Alias for `intersection(s1, s2) <#intersection,BBTree[K,V],BBTree[K,V]>`_.
//     return intersection(s1, s2)
// 
// def `-`(s1, s2): // -> BBTree[K,V]
//     // Alias for `difference(s1, s2) <#difference,BBTree[K,V],BBTree[K,V]>`_.
//     return difference(s1, s2)
// 
// // A -+- B  ==  (A - B) + (B - A)  ==  (A + B) - (A * B)
// 
// def `-+-`(s1, s2): // -> BBTree[K,V]
//     // Alias for `symmetricDifference(s1, s2) <#symmetricDifference,BBTree[K,V],BBTree[K,V]>`_.
//     return symmetricDifference(s1, s2)
// 
// def `<`(s1: BBTree[K,U], s2): // -> bool
//     // Alias for `isProperSubset(s1, s2) <#isProperSubset,BBTree[K,U],BBTree[K,V]>`_.
//     // Returns true if the keys in `s1` form a strict or proper subset of the keys in `s2`.
//     //
//     // A strict or proper subset `s1` has all of its keys in `s2` but `s2` has
//     // more elements than `s1`.
//     return isProperSubset(s1, s2)
// 
// def `<=`(s1: BBTree[K,U], s2): // -> bool
//     // Alias for `isSubset(s1, s2) <#isSubset,BBTree[K,U],BBTree[K,V]>`_.
//     // Returns true if `s1` is subset of `s2`.
//     //
//     // A subset `s1` has all of its members in `ts2` and `s2` doesn't necessarily
//     // have more members than `s1`. That is, `s1` can be equal to `s2`.
//     return isSubset(s1, s2)
// 
// /*
// //  `==` seems like an extreme assertion when values are not being considered...
// //  but this would be consistent with Nim's set API. Punt for now; use =?= instead.
// //
// def `==`(s1: BBTree[K,U], s2): bool =
//     // Returns true if both `s1` and `s2` have the same keys and set size.
//     result = setEqual(s1, s2)
// */
// def `=?=`(s1: BBTree[K,U], s2): bool =
//     // Alias for `setEqual(s1, s2) <#setEqual,BBTree[K,U],BBTree[K,V]>`_.
//     // Returns true if both `s1` and `s2` have the same keys and set size.
//     return setEqual(s1, s2)

/* **************************** convenience funcs ********************************
*/

def toSet(keys): // -> BBTree<K,bool>
  // Creates a BBTree set that contains the given `keys` with value `true`.
  //
  // Example:
  //   let numbers = toSet(["1", "2", "3", "4", "5"])
  //   assert(numbers.contains("2"))
  //   assert(numbers.contains("4"))
  var result:BBTree? = nil
  for(keys) key: result = add(result, key, true)
  return result

/* **************************** for unit tests ********************************
*/

def countKeys(root) -> int:
    // Used for unit testing only; normally use `len` to get the number of keys.
    var node = root
    var result = 0
    while node:
        result += countKeys(node.left)
        result += 1
        node = node.right
    return result

def balanced(node) -> int: // returns size in nodes or -1 for error
    if node:
        let sl = nodeSize(node.left)
        let sr = nodeSize(node.right)
        let sz = nodeSize(node)
        if sz != (sl + 1 + sr):
            // fprintf(stderr, "Error in bbwatree balanced: %u != %u + 1 + %u; (%u %u)\n", sz, sl, sr, nx->left, nx->right);
            return -1
        if (sl + sr) <= 1:
            // balanced
            nil
        else: if sr > (omega * sl):
            // fprintf(stderr, "Error in bbwatree balanced: sr %u > omega * %u\n", sr, sl);
            return -1
        else: if sl > (omega * sr):
            // fprintf(stderr, "Error in bbwatree balanced: sl %u > omega * %u\n", sl, sr);
            return -1
        
        let slb = balanced(node.left)
        let srb = balanced(node.right)
        if (slb < 0) or (sl != slb):
            // if (slb >= 0) fprintf(stderr, "Error in bbwatree balanced: sl %u != %lld\n", sl, slb);
            return -1
        if (srb < 0) or (sr != srb):
            // if (srb >= 0) fprintf(stderr, "Error in bbwatree balanced: sr %u != %lld\n", sr, srb);
            return -1
        return sz
    else:
        return 0        

def isBalanced(root) -> bool:
    // Used for unit testing only; returns `true` if the tree is balanced, which should always
    // be the case.
    let size = balanced(root)
    if not root:
        return (size == 0)
    return (size > 0) and (size == nodeSize(root))

/* ***************************** sanity check ********************************
*/

// when isMainModule:
// 
//     proc test1() =
//         var
//             tre0 : BBTree[string,int] = nil
//             tre1 = add(tre0, "hello", 1) // instantiate a BBTree with ("hello",1)
//             tre2 = add(tre1, "world", 1) // add ("world",2)
//         for str,num in inorder(tre2):
//             stdout.writeLine(str)
//     test1()
//     echo "done"


def test1():
    //class BBTree_s_i = BBTree<string,int>
    //let tre0 = nil::BBTree_s_i //ng
    let tre0 = nil::BBTree
    let tre1 = add(tre0, "hello", 1) // instantiate a BBTree with ("hello",1)
    let tre2 = add(tre1, "world", 2) // add ("world",2)
    //print tre2 //ok
    map(tre2): print(_k); print(_v); true
    //ok foldr(tre2, false): print(_k); true
    //ok foldl(tre2, false): print(_k); true
    foreach(tre2): print(_); true

    //let f = def(k,v,b): concat_string([b,k],":")
    //print(foldl(tre2, "keys", f))
    print(foldl(tre2, "keys") k, v, b: v; concat_string([b, k],":"))

    // segfault:
    // print(foldl(tre2, "keys"): def(k,v,b): concat_string([b,k],":"))

    print(foldl(tre2, 0): _a; _b + _c)

    let tre3 = del(tre2, "hello")
    print tre3

test1()
print("done")

/* ******************************** notes ***********************************

// For a bbwa tree, the max depth is log2(n) / log2(1 + 1/ω)
// With omega at 3, log2(1 + 1/ω) = log2(1 + 1/3) = 0.41503749927884
// The upper bound on depth is 2.41 * log2(n)

*/
