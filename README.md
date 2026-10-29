# chicken-champ-tree

An unordered persistent dictionary data structure based on CHAMP
tries, a sibling library to
[chicken-rbtree](https://github.com/iraikov/chicken-rbtree).

## Usage

```scheme
(import champ-tree)
```

## Documentation

`champ-tree` implements CHAMP (Compressed Hash-Array Mapped
Prefix-tree), the memory- and iteration-friendly variant of a HAMT
(Hash Array Mapped Trie) described by Steindorfer and Vinju,
"Optimizing Hash-Array Mapped Tries for Fast and Lean Immutable JVM
Collections" (OOPSLA 2015).

The present implementation code defines a persistent map class that
implements an unordered dictionary mapping of keys to values,
analogous to `rb-tree`'s ordered dictionary but backed by a hash trie
instead of a red-black tree. Looking up, inserting, or deleting an
arbitrary key takes time proportional to a small constant trie depth
(at most 7 levels), averaging O(1), instead of `rb-tree`'s O(log n) --
the price is that there is no key ordering: there is no `get-min`,
`get-max`, or range scan, and traversal order is not meaningful
relative to key values. The union operations take time roughly linear
in the total size of the two maps.

### Procedures

The persistent map instance is created by procedure `champ-tree-map`:

```
champ-tree-map :: KEY-HASH-PROC KEY-EQUAL-PROC -> persistent-unordered-map
```

where `KEY-HASH-PROC` is a user-supplied function that takes a key and
returns a hash value (any non-negative integer; it is masked to 32
bits internally), and `KEY-EQUAL-PROC` is a user-supplied equality
predicate for keys, used to resolve a shared hash between two keys. A
convenience constructor is also provided for the common case of
`equal?`-comparable keys:

```
champ-tree-map/equal :: -> persistent-unordered-map
```

which uses SRFI 69's `hash` and R7RS `equal?`. All maps are
persistent: the operations that change a map return a new map and
leave the original unmodified.

`persistent-unordered-map` is a yasos class, deliberately named
differently from `rb-tree`'s `persistent-map` class so the two can
coexist (and so a caller can tell which kind of map a value is), that
contains the following operations:

* `persistent-unordered-map? OBJ` : returns `#t` if `OBJ` is a persistent unordered map.
* `empty? MAP` : returns `#t` if the map has no associations.
* `size MAP` : returns the number of associations in the map.
* `get MAP KEY` : returns the (key . value) pair of the association with the given `KEY`. If there is no such association, an error is signalled.
* `get/default MAP KEY DEFAULT` : as `get`, but returns `DEFAULT` if there is no association with `KEY`. If `DEFAULT` is a procedure, it is called with no arguments and its result is returned.
* `get-value MAP KEY` : returns the value of the association with the given `KEY`. If there is no such association, an error is signalled.
* `get-value/default MAP KEY DEFAULT` : as `get-value`, but returns `DEFAULT` (or the result of calling it, if it is a procedure) if there is no association with `KEY`.
* `put MAP KEY VALUE` : returns a new map that contains the given association. If the key was already in the map, its association is replaced.
* `update MAP KEY VALUE MERGE-FN` : returns a new map that contains the given association. If the key was already in the map, `(MERGE-FN VALUE OLD-VALUE)` gives the new value.
* `generate MAP P F G SEED` : starting from `SEED`, adds the association `(F SEED)`, a (key . value) pair, to the map and continues with `(G SEED)`, until `(P SEED)` is true. Returns the new map.
* `delete MAP KEY` : returns a pair `(ASSOCIATION . NEW-MAP)`, where `ASSOCIATION` is the deleted (key . value) pair and `NEW-MAP` no longer contains it. If the key is not in the map, an error is signalled.
* `for-each-assoc MAP PROC` : applies `PROC` to each (key . value) association of the map, in the trie's own layout order. This order is unspecified relative to the keys' values, but deterministic for a given final set of associations: two maps with the same associations traverse in the same order regardless of how they were built. Does nothing on an empty map.
* `gen-assoc MAP` : returns a generator, a procedure of no arguments, that returns the (key . value) associations of the map in the same order as `for-each-assoc`, and then an end-of-file object.
* `map-key-hash MAP` : returns the key-hash procedure the map was created with.
* `map-key-equal MAP` : returns the key-equal procedure the map was created with.

The map also implements these operations of `yasos-collections`:
`collection?`, `gen-keys` and `gen-elts` (generators of the keys and of
the values, in the same unordered-but-deterministic order as
`for-each-assoc`), and `for-each-key` and `for-each-elt`.

### Unions

Each union takes two maps `M1` and `M2`, which must share the same
key-hash and key-equal procedures (checked, and an error is signalled
on a mismatch, since a hash mismatch would silently corrupt structure
rather than merely disorder results), and returns a new map whose keys
are the union of their keys. The new map uses the key-hash/key-equal
of `M1`. Neither input is modified.

* `((union-with MERGE-FN) M1 M2)` : `(MERGE-FN X Y)` gives the value of a key that is in both maps, where `X` is its value in `M1` and `Y` its value in `M2`. Keys in only one map keep their value.
* `((union-withi MERGE-FN) M1 M2)` : as `union-with`, but `MERGE-FN` also receives the key: `(MERGE-FN KEY X Y)`.
* `((union-transform FN MERGE-FN) M1 M2)` : the value of a key in only one map becomes `(FN X)`, and the value of a key in both maps becomes `(MERGE-FN X Y)`. Returns a list `(N M KT1 KT2)`, where `N` is the number of keys in the new map `M`. `KT1` is a list of `(X . NEW-VALUE)` pairs that relates each value `X` of `M1` to its value in `M`, and `KT2` is the corresponding list for `M2`. A key in both maps contributes a pair to both lists. Unlike `rb-tree`'s `union-transform`, `KT1`/`KT2`'s order is **not** ascending by key -- there is no key order in a hash map. The order is unspecified relative to key values, but deterministic for a given pair of input maps and a given key-hash procedure.

### Checking a map

* `champ-tree-map-valid? MAP` : returns `#t` if the trie of `MAP` satisfies every CHAMP structural invariant (bitmap/array consistency, hash-chunk correctness along every path, canonical form, no duplicate keys). It is intended for testing.
* `champ-tree-map-equal? M1 M2` : returns `#t` if `M1` and `M2` have the same set of (key . value) associations (values compared with `equal?`). When both maps share the same key-hash/key-equal procedures, this uses CHAMP's canonical form for an efficient structural comparison; otherwise it falls back to a linear check.
