# lobster-bbtree

BBTree is a Bounded Balance Tree library for the [Lobster programming language](https://github.com/aardappel/lobster).

## Status

The non-generic BBTree<string><int> version of BBTree is working. Improvements to Lobster are planned 
that should enable generic trees.

## BBTree Overview

BBTrees, also known as Weight Balanced Trees, or Adams Trees, are a persistent data structure
with a nice combination of properties:

* Generic (parameterized) key,value map
* Insert (`add`), lookup (`get`), and delete (`del`) in O(log(N)) time
* Key-ordered iterators (`inorder` and `revorder`)
* Lookup by relative position from beginning or end (`getNth`) in O(log(N)) time
* Get the position (`rank`) by key in O(log(N)) time
* Efficient set operations using tree keys
* Map extensions to set operations with optional value merge control for duplicates

By "persistent" we mean that the BBTree always preserves the previous version of itself when it is modified. 
As such it is effectively immutable, as the operations do not (visibly) update the structure in-place, 
but instead always yield a new updated structure.

The BBTree data structure resides in heap memory, and is destroyed by the garbage collector when there 
are no longer any program references to it. When insertions or deletions to the tree are made, we 
attempt to reuse as much of the old structure as possible.

Because the BBTree is never mutated a BBTree may be shared across threads safely (though updates 
in one thread will not be visible in another until the modified tree is shared once again).

## BBTree Credits

References:

*Implementing Sets Efficiently in a Functional Language*
Stephen Adams
CSTR 92-10
Department of Electronics and Computer Science University of Southampton Southampton S09 5NH

*Adams’ Trees Revisited Correct and Efficient Implementation*
Milan Straka
Department of Applied Mathematics Charles University in Prague, Czech Republic

[Weight-balanced trees](https://en.wikipedia.org/wiki/Weight-balanced_tree) on Wikipedia

## BBTree Details

### Documentation

For now, you can view [Nim docs](http://htmlpreview.github.io/?https://github.com/dcurrie/nim-bbtree/blob/master/src/bbtree.html)

### Installation

TODO

### Test

See `bbtest.lobster`

### License

MIT. See file LICENSE.
