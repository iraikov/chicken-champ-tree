;;
;; CHAMP tree (Compressed Hash-Array Mapped Prefix-tree)
;;
;; An implementation of an unordered persistent dictionary data
;; structure, based on CHAMP tries (Steindorfer & Vinju, "Optimizing
;; Hash-Array Mapped Tries for Fast and Lean Immutable JVM
;; Collections", OOPSLA 2015), a memory- and iteration-friendly
;; variant of a HAMT (Bagwell's Hash Array Mapped Trie).
;;
;; This library is a sibling of chicken-rbtree: it exposes the same
;; style of Yasos-object persistent-map interface, but is backed by a
;; hash trie instead of a red-black tree, so lookups, insertions and
;; deletions are O(1) on average (bounded by a small constant trie
;; depth) instead of O(log n), at the cost of giving up key ordering.
;;
;; Copyright 2026 Ivan Raikov.
;;
;;
;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of the
;; License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; A full copy of the GPL license can be found at
;; <http://www.gnu.org/licenses/>.
;;

(module champ-tree

	(
	 champ-tree-map champ-tree-map/equal
	 union-with union-withi union-transform
	 persistent-unordered-map? get get/default get-value get-value/default
	 put generate update delete
	 for-each-assoc gen-assoc
	 map-key-hash map-key-equal
	 champ-tree-map-valid? champ-tree-map-equal?
         )


  (import scheme (chicken base)
          (scheme base)
          (chicken fixnum)
          (chicken bitwise)
          (chicken memory representation)
          (only (chicken string) conc)
          datatype matchable yasos yasos-collections
          (only srfi-1 any every) (srfi 69))
  (import-for-syntax srfi-1)

;;
;; Persistent map operations
;;
;; A persistent-unordered-map provides the operations provided by
;; yasos-collections, plus the following operations:
;;
;;	get
;;
;;		procedure LAMBDA KEY . DEFAULT-CLAUSE which searches
;;		the given map for an association with a given KEY, and
;;		returns a (key . value) pair of the found association.
;;		If an association with the KEY cannot be located,
;;		the PROC returns the result of evaluating the
;;		DEFAULT-CLAUSE.  If the default clause is omitted, an
;;		error is signalled.
;;
;;	for-each-assoc
;;
;;		a procedure LAMBDA PROC that applies PROC to every
;;		(key . value) association in the map, in the trie's
;;		own layout order (lowest bitmap bit first at each
;;		node, inlined data entries before sub-node entries).
;;		This order is unspecified relative to the keys'
;;		values, but is deterministic for a given final set of
;;		associations: because CHAMP tries are kept in
;;		canonical form, two maps with the same associations
;;		have the identical trie shape regardless of the
;;		sequence of put/delete operations used to build them,
;;		and therefore traverse in the same order.
;;
;;	gen-assoc
;;
;;		a procedure LAMBDA () that returns a generator of
;;		every (key . value) association in the map, in the
;;		same order as for-each-assoc.  The generator returns
;;		an end-of-file object when exhausted.
;;
;;	map-key-hash
;;
;;		returns the key-hash procedure the map was created
;;		with.
;;
;;	map-key-equal
;;
;;		returns the key-equal procedure the map was created
;;		with.
;;

(define-predicate persistent-unordered-map?)
(define-operation (get pmap key))
(define-operation (get/default pmap key default-clause))
(define-operation (get-value pmap key))
(define-operation (get-value/default pmap key default-clause))
(define-operation (generate pmap p f g seed))
(define-operation (put pmap key value))
(define-operation (update pmap key value merge-fn))
(define-operation (delete pmap key))
(define-operation (for-each-assoc pmap f))
(define-operation (gen-assoc pmap))
(define-operation (map-root pmap))
(define-operation (map-key-hash pmap))
(define-operation (map-key-equal pmap))


(define (champ-tree:error x . rest)
  (let ((port (open-output-string)))
    (let loop ((objs (cons x rest)))
      (if (null? objs)
	  (begin
	    (newline port)
	    (error 'champ-tree (get-output-string port)))
	  (begin (display (car objs) port)
		 (display " " port)
		 (loop (cdr objs)))))))


;;
;; Bitmap / hash-chunk constants and helpers
;;

;; 5 bits per trie level (32-way branching).  A key's hash is masked
;; to 32 bits and consumed 5 bits at a time; +max-depth+ is the depth
;; at which the 32-bit hash is exhausted, past which two distinct
;; hashes can no longer be distinguished by any chunk and must be
;; resolved by a collision-node instead of further branching.
(define +bits-per-level+ 5)
(define +level-mask+     #x1F)
(define +hash-mask+      #xFFFFFFFF)
(define +max-depth+      7)

(define (mask32 h) (bitwise-and h +hash-mask+))

(define (hash-chunk h depth)
  (fxand (fxshr h (fx* +bits-per-level+ depth)) +level-mask+))

;; A 256-entry byte-popcount lookup table, built once at module load
;; (the idea is borrowed from the iset egg's own byte-oriented
;; bit-count table, adapted here for packed 32-bit fixnums).
(define +byte-popcount-table+
  (let ((table (make-vector 256 0)))
    (do ((i 0 (fx+ i 1)))
	((fx= i 256) table)
      (vector-set! table i
		   (let loop ((n i) (c 0))
		     (if (fx= n 0) c (loop (fxand n (fx- n 1)) (fx+ c 1))))))))

(define (popcount32 n)
  (fx+ (fx+ (vector-ref +byte-popcount-table+ (fxand n #xFF))
	    (vector-ref +byte-popcount-table+ (fxand (fxshr n 8) #xFF)))
       (fx+ (vector-ref +byte-popcount-table+ (fxand (fxshr n 16) #xFF))
	    (vector-ref +byte-popcount-table+ (fxand (fxshr n 24) #xFF)))))

(define (bit-set? bitmap b) (not (fx= 0 (fxand bitmap (fxshl 1 b)))))

;; Index, within a node's flat array, of the data-run slot for bit b.
;; DATAMAP is the bitmap of inlined-data bits; the formula is valid
;; whether or not bit b is itself set in DATAMAP, since the mask
;; excludes bit b.
(define (data-index datamap b)
  (fx* 2 (popcount32 (fxand datamap (fx- (fxshl 1 b) 1)))))

;; Index, within a node's flat array, of the node-run slot for bit b.
(define (node-index datamap nodemap b)
  (fx+ (fx* 2 (popcount32 datamap))
       (popcount32 (fxand nodemap (fx- (fxshl 1 b) 1)))))


;;
;; Node representation
;;
;; A bitmap-node has two disjoint 32-bit bitmaps: DATAMAP marks slots
;; holding an inlined (key . value) pair, NODEMAP marks slots holding
;; a pointer to a child node one level deeper.  ARRAY is one flat
;; vector: first the data run (2*popcount(datamap) elements, key/value
;; interleaved, in increasing bit order), then the node run
;; (popcount(nodemap) elements, in increasing bit order).
;;
;; A collision-node holds two or more (key . value) pairs whose hashes
;; are fully equal (not merely equal through some depth); it can
;; therefore appear at any depth, not only at +max-depth+ -- see
;; two-entry-node below.
;;
;; The map's root is always one of three shapes: #f (empty), a bare
;; (key . value) pair (exactly one association in the whole map), or a
;; bitmap-node/collision-node with two or more associations.  This
;; avoids a root/non-root special case in the canonical-form
;; invariant: every bitmap-node that is NOT the root must never be a
;; lone single-data-entry wrapper (popcount(datamap) = 1 and
;; popcount(nodemap) = 0) -- such a node's one entry must instead be
;; inlined directly into its parent's data run.

(define-record-type bitmap-node
  (BitmapNode datamap nodemap array)
  bitmap-node?
  (datamap bitmap-node-datamap)
  (nodemap bitmap-node-nodemap)
  (array   bitmap-node-array))

(define-record-type collision-node
  (CollisionNode hash entries)
  collision-node?
  (hash    collision-node-hash)
  (entries collision-node-entries))

(define (Empty) #f)

(define (trie-node? x) (or (bitmap-node? x) (collision-node? x)))

;; #t iff x is the bare-pair singleton-root shape (not a trie node).
(define (assoc-pair? x) (and (pair? x) (not (trie-node? x))))

(set-record-printer! bitmap-node
  (lambda (x out)
    (display "#(BitmapNode " out)
    (display (conc (number->string (bitmap-node-datamap x) 16) " ") out)
    (display (conc (number->string (bitmap-node-nodemap x) 16) " ") out)
    (display (bitmap-node-array x) out)
    (display ")" out)))

(set-record-printer! collision-node
  (lambda (x out)
    (display "#(CollisionNode " out)
    (display (conc (number->string (collision-node-hash x) 16) " ") out)
    (display (collision-node-entries x) out)
    (display ")" out)))


;;
;; Small vector-splice helper used throughout insert/delete/union:
;; returns a new vector equal to VEC with COUNT elements starting at
;; POS removed and the elements of INSERT-LIST spliced in at POS.
;; Used for plain removal (insert-list = '()), plain insertion
;; (count = 0), and same-size in-place-looking replacement
;; (count = (length insert-list)); the node arrays are always small
;; (at most 64 elements), so building the result via vector-append is
;; simple and fast enough.
(define (vector-splice vec pos count insert-list)
  (vector-append (vector-copy vec 0 pos)
		  (list->vector insert-list)
		  (vector-copy vec (fx+ pos count) (vector-length vec))))

(define (vector-copy-replace vec pos x)
  (let ((new (vector-copy vec)))
    (vector-set! new pos x)
    new))


;; Builds the smallest subtrie holding exactly two associations whose
;; full (masked) hashes are H1 and H2, starting the search for a
;; distinguishing chunk at DEPTH.  If H1 and H2 are fully equal, no
;; depth of chunking can ever separate them, so a collision-node is
;; returned immediately regardless of DEPTH -- this is what allows a
;; collision-node to appear shallower than +max-depth+ (including, in
;; the degenerate case of a two-key, fully-colliding map, as the map's
;; own root).  Otherwise H1 and H2 are guaranteed to differ in some
;; chunk at a depth <= +max-depth+ - 1 = 6, since they differ in some
;; bit among the 32 masked bits and +max-depth+ levels of 5 bits cover
;; all 32 bits; reaching +max-depth+ with H1 still /= H2 therefore
;; indicates an internal invariant violation, not a legitimate case.
(define (two-entry-node depth h1 key1 value1 h2 key2 value2)
  (cond
   ((fx= h1 h2) (CollisionNode h1 (list (cons key1 value1) (cons key2 value2))))
   ((fx= depth +max-depth+)
    (champ-tree:error 'insert "distinct hashes still unresolved at max depth"))
   (else
    (let ((b1 (hash-chunk h1 depth)) (b2 (hash-chunk h2 depth)))
      (cond
       ((fx= b1 b2)
	(BitmapNode 0 (fxshl 1 b1)
		    (vector (two-entry-node (fx+ depth 1) h1 key1 value1 h2 key2 value2))))
       ((fx< b1 b2)
	(BitmapNode (fxior (fxshl 1 b1) (fxshl 1 b2)) 0 (vector key1 value1 key2 value2)))
       (else
	(BitmapNode (fxior (fxshl 1 b1) (fxshl 1 b2)) 0 (vector key2 value2 key1 value1))))))))


;; Separates an existing subtree (all of whose keys share the single
;; hash EXISTING-HASH -- in practice always a collision-node, whose
;; entries are by construction all hash-equal to each other) from one
;; new (KEY2 . VALUE2) association whose hash H2 differs from
;; EXISTING-HASH.  Unlike two-entry-node's same-bitmap two-key split,
;; the two sides here land in DIFFERENT bitmaps (one data slot, one
;; node slot) whenever their chunks first diverge, so there is no
;; need to compare b1 and b2 to decide array order -- data and node
;; runs are separate arrays-within-the-array regardless of which bit
;; is numerically larger.  This is what lets node-insert place a
;; genuinely new, differently-hashed key alongside an existing
;; collision-node instead of erroring, which matters both for plain
;; insert (a collision-node can sit at any depth, including the map's
;; own root, per two-entry-node's shortcut above) and for the union
;; engine's build-node-from-entries.
(define (split-node-vs-subtree depth existing-hash existing-subtree h2 key2 value2)
  (if (fx= depth +max-depth+)
      (champ-tree:error 'insert "distinct hashes still unresolved at max depth")
      (let ((b1 (hash-chunk existing-hash depth)) (b2 (hash-chunk h2 depth)))
	(if (fx= b1 b2)
	    (BitmapNode 0 (fxshl 1 b1)
			(vector (split-node-vs-subtree (fx+ depth 1) existing-hash existing-subtree h2 key2 value2)))
	    (BitmapNode (fxshl 1 b2) (fxshl 1 b1) (vector key2 value2 existing-subtree))))))


;;
;; Adds a new association to a node, or replaces/merges the old value
;; if the key was already present.  VALUE-MERGE is called as
;; (value-merge new-value old-value); put uses (lambda (x ax) x),
;; update uses the user's merge-fn, mirroring rb-tree's insert.
;;
;; node-insert is written in a more general form than plain
;; put/update need, taking ON-NEW (called as (on-new key value) to
;; produce the value to store when key is not already present) and
;; ON-CONFLICT (called as (on-conflict key value old-value) to
;; produce the value to store when key IS already present).  Plain
;; insert (below) always passes on-new = (lambda (k v) v); the union
;; engine (section 4) reuses node-insert as its insert-into-node
;; primitive with a non-trivial on-new, so that a lone data entry from
;; one side can be merged into the other side's subtree through
;; on-left/on-right/on-both without duplicating this traversal logic.
(define (node-insert key-hash key-equal on-new on-conflict node depth h key value)
  (if (collision-node? node)
      (if (not (fx= h (collision-node-hash node)))
	  ;; KEY merely shares the chunk-prefix down to DEPTH with this
	  ;; collision-node's keys, without being a full hash collision
	  ;; with them -- a perfectly ordinary case (e.g. a collision-
	  ;; node formed early via two-entry-node's full-hash shortcut,
	  ;; followed by an unrelated key that happens to share only the
	  ;; chunks visited so far), not an error.
	  (split-node-vs-subtree depth (collision-node-hash node) node h key (on-new key value))
	  (let ((entries (collision-node-entries node)))
	    (let loop ((es entries) (acc '()))
	      (cond
	       ((null? es)
		(CollisionNode h (cons (cons key (on-new key value)) entries)))
	       ((key-equal key (car (car es)))
		(CollisionNode h (append (reverse acc)
					  (cons (cons key (on-conflict key value (cdr (car es))))
						(cdr es)))))
	       (else (loop (cdr es) (cons (car es) acc)))))))
      (let* ((datamap (bitmap-node-datamap node))
	     (nodemap (bitmap-node-nodemap node))
	     (array   (bitmap-node-array node))
	     (b       (hash-chunk h depth)))
	(cond
	 ((bit-set? datamap b)
	  (let* ((di (data-index datamap b))
		 (k0 (vector-ref array di))
		 (v0 (vector-ref array (fx+ di 1))))
	    (if (key-equal key k0)
		(BitmapNode datamap nodemap
			    (vector-splice array di 2 (list key (on-conflict key value v0))))
		(let* ((child (two-entry-node (fx+ depth 1)
					       h key (on-new key value)
					       (mask32 (key-hash k0)) k0 v0))
		       (array1 (vector-splice array di 2 '()))
		       (new-datamap (fxand datamap (fxnot (fxshl 1 b))))
		       (new-nodemap (fxior nodemap (fxshl 1 b)))
		       (pos (fx+ (fx* 2 (popcount32 new-datamap))
				 (popcount32 (fxand nodemap (fx- (fxshl 1 b) 1))))))
		  (BitmapNode new-datamap new-nodemap
			      (vector-splice array1 pos 0 (list child)))))))
	 ((bit-set? nodemap b)
	  (let* ((ni (node-index datamap nodemap b))
		 (child  (vector-ref array ni))
		 (child1 (node-insert key-hash key-equal on-new on-conflict child (fx+ depth 1) h key value)))
	    (BitmapNode datamap nodemap (vector-copy-replace array ni child1))))
	 (else
	  (let* ((new-datamap (fxior datamap (fxshl 1 b)))
		 (di (data-index datamap b)))
	    (BitmapNode new-datamap nodemap (vector-splice array di 0 (list key (on-new key value))))))))))


;; Top-level insert, handling the three root shapes.  Returns the new
;; root (never mutates ROOT).
(define (insert key-hash key-equal value-merge root key value)
  (let ((h (mask32 (key-hash key))))
    (cond
     ((not root) (cons key value))
     ((assoc-pair? root)
      (let ((k0 (car root)) (v0 (cdr root)))
	(if (key-equal key k0)
	    (cons key (value-merge value v0))
	    (two-entry-node 0 h key value (mask32 (key-hash k0)) k0 v0))))
     (else (node-insert key-hash key-equal (lambda (k v) v) (lambda (k new old) (value-merge new old))
			root 0 h key value)))))


;; Looks for an item: given a key, returns the corresponding (key
;; . value) association, or #f if the map does not contain it.
(define (find-assoc key-hash key-equal root key)
  (and root
       (if (assoc-pair? root)
	   (and (key-equal key (car root)) root)
	   (let ((h (mask32 (key-hash key))))
	     (let recur ((node root) (depth 0))
	       (if (collision-node? node)
		   (assoc key (collision-node-entries node) key-equal)
		   (let* ((datamap (bitmap-node-datamap node))
			  (nodemap (bitmap-node-nodemap node))
			  (array   (bitmap-node-array node))
			  (b       (hash-chunk h depth)))
		     (cond
		      ((bit-set? datamap b)
		       (let* ((di (data-index datamap b))
			      (k0 (vector-ref array di)))
			 (and (key-equal key k0)
			      (cons k0 (vector-ref array (fx+ di 1))))))
		      ((bit-set? nodemap b)
		       (recur (vector-ref array (node-index datamap nodemap b)) (fx+ depth 1)))
		      (else #f)))))))))


(define (find-ref key-hash key-equal root key)
  (let ((item (find-assoc key-hash key-equal root key)))
    (and item (cdr item))))


;;
;; Finds an association with a given key and deletes it.  Returns the
;; (key . value) pair of the deleted association together with the
;; new root, or #f if the key was not found.  Deletion is strictly
;; local to the root-to-leaf path (no global rebalancing, unlike
;; red-black deletion): a child that collapses to a canonical
;; single-data-entry shape (or a collision-node that shrinks to a
;; single entry) is inlined into its PARENT's data run by the caller,
;; one level up, which is the only re-canonicalization step needed.
;;
;; node-delete returns #f if the key was not found in NODE, or a pair
;; (deleted-item . new-node-or-replacement), where new-node-or-
;; replacement is itself either a trie node (>= 2 entries remain in
;; this subtree) or a bare (key . value) pair (exactly one entry
;; remains in this subtree, signalling to the caller that it must be
;; inlined), or #f (this subtree became empty, only possible for a
;; node directly beneath a bitmap-node that had exactly this one child
;; and no data entries of its own -- see the nodemap-bit branch below).

;; Builds the post-removal result for a bitmap-node from a fresh
;; (DATAMAP, NODEMAP, ARRAY) triple that has already had the deleted
;; entry or child spliced out.  Returns #f if nothing remains, a bare
;; (key . value) pair if exactly one association remains -- signalling
;; to the CALLER that it must inline that pair into its own data run,
;; the same canonicalization step delete must perform whenever a
;; subtree shrinks to a single entry -- or the bitmap-node itself when
;; two or more associations remain.  Every site in node-delete that
;; constructs a new bitmap-node after removing something goes through
;; this helper, so the collapse check is never accidentally skipped.
(define (make-node-or-collapse datamap nodemap array)
  (cond
   ((and (fx= 0 datamap) (fx= 0 nodemap)) #f)
   ((and (fx= 1 (popcount32 datamap)) (fx= 0 nodemap))
    (cons (vector-ref array 0) (vector-ref array 1)))
   (else (BitmapNode datamap nodemap array))))

(define (node-delete key-hash key-equal node depth h key)
  (if (collision-node? node)
      (let ((entries (collision-node-entries node)))
	(let loop ((es entries) (acc '()))
	  (cond
	   ((null? es) #f)
	   ((key-equal key (car (car es)))
	    (let ((remaining (append (reverse acc) (cdr es))))
	      (cons (car es)
		    (if (null? (cdr remaining))
			(car remaining)                      ; collapse to bare pair
			(CollisionNode (collision-node-hash node) remaining)))))
	   (else (loop (cdr es) (cons (car es) acc))))))
      (let* ((datamap (bitmap-node-datamap node))
	     (nodemap (bitmap-node-nodemap node))
	     (array   (bitmap-node-array node))
	     (b       (hash-chunk h depth)))
	(cond
	 ((bit-set? datamap b)
	  (let* ((di (data-index datamap b))
		 (k0 (vector-ref array di))
		 (v0 (vector-ref array (fx+ di 1))))
	    (and (key-equal key k0)
		 (let ((new-datamap (fxand datamap (fxnot (fxshl 1 b))))
		       (array1 (vector-splice array di 2 '())))
		   (cons (cons k0 v0) (make-node-or-collapse new-datamap nodemap array1))))))
	 ((bit-set? nodemap b)
	  (let* ((ni    (node-index datamap nodemap b))
		 (child (vector-ref array ni))
		 (result (node-delete key-hash key-equal child (fx+ depth 1) h key)))
	    (and result
		 (let ((item (car result)) (new-child (cdr result)))
		   (cons item
			 (cond
			  ;; child subtree emptied entirely
			  ((not new-child)
			   (let ((new-nodemap (fxand nodemap (fxnot (fxshl 1 b))))
				 (array1 (vector-splice array ni 1 '())))
			     (make-node-or-collapse datamap new-nodemap array1)))
			  ;; child collapsed to a single association: inline it
			  ((assoc-pair? new-child)
			   (let* ((array1 (vector-splice array ni 1 '()))
				  (new-nodemap (fxand nodemap (fxnot (fxshl 1 b))))
				  (new-datamap (fxior datamap (fxshl 1 b)))
				  (pos (data-index datamap b)))
			     (make-node-or-collapse
			      new-datamap new-nodemap
			      (vector-splice array1 pos 0 (list (car new-child) (cdr new-child))))))
			  ;; child still a real node with >= 2 entries
			  (else
			   (BitmapNode datamap nodemap (vector-copy-replace array ni new-child)))))))))
	 (else #f))))) ;; key not present in this node


(define (delete-assoc key-hash key-equal root key)
  (cond
   ((not root) #f)
   ((assoc-pair? root)
    (and (key-equal key (car root)) (cons root #f)))
   (else
    (let* ((h (mask32 (key-hash key)))
	   (result (node-delete key-hash key-equal root 0 h key)))
      (and result (cons (car result) (cdr result)))))))


(define (apply-default-clause label key default-clause)
  (cond
   ((null? default-clause)
    (champ-tree:error label "key " key " was not found in the map"))
   ((pair? (cdr default-clause))
    (champ-tree:error label "default argument must be a single clause"))
   ((procedure? (car default-clause)) ((car default-clause)))
   (else (car default-clause))))


;;
;; Whole-trie association count, by brute-force walk (there is no
;; cached size field on any node, the same O(n) `size` tradeoff
;; rb-tree makes, kept consistent between the two libraries).

(define (get-size root)
  (cond
   ((not root) 0)
   ((assoc-pair? root) 1)
   ((collision-node? root) (length (collision-node-entries root)))
   (else
    (let* ((datamap (bitmap-node-datamap root))
	   (nodemap (bitmap-node-nodemap root))
	   (array   (bitmap-node-array root))
	   (ndata   (popcount32 datamap))
	   (nnode   (popcount32 nodemap)))
      (let loop ((i 0) (acc ndata))
	(if (fx= i nnode)
	    acc
	    (loop (fx+ i 1) (fx+ acc (get-size (vector-ref array (fx+ (fx* 2 ndata) i)))))))))))

(define (get-depth root)
  (cond
   ((not root) 0)
   ((assoc-pair? root) 1)
   ((collision-node? root) 1)
   (else
    (let* ((datamap (bitmap-node-datamap root))
	   (nodemap (bitmap-node-nodemap root))
	   (array   (bitmap-node-array root))
	   (ndata   (popcount32 datamap))
	   (nnode   (popcount32 nodemap)))
      (let loop ((i 0) (acc 0))
	(if (fx= i nnode)
	    (fx+ 1 acc)
	    (loop (fx+ i 1) (fxmax acc (get-depth (vector-ref array (fx+ (fx* 2 ndata) i)))))))))))


;;
;; Traversal and generators
;;
;; Stack frames are either an (Assoc pair) ready to yield directly
;; (the bare-pair singleton-root shape, or one entry at a time out of
;; a collision-node), or a (Node node slot), a bitmap-node together
;; with the next array index still to be visited.  This is the
;; trie-stack analogue of rb-tree's BST-stack generator idiom: push-
;; first descends into the next child before continuing past it,
;; exactly as range-push-left descends into node-left before queuing
;; node-right.

(define-record-type assoc-frame
  (Assoc pair)
  assoc-frame?
  (pair assoc-frame-pair))

(define-record-type collision-frame
  (Collision entries)
  collision-frame?
  (entries collision-frame-entries))

(define-record-type node-frame
  (Node node slot)
  node-frame?
  (node node-frame-node)
  (slot node-frame-slot))

(define (push-first root stack)
  (cond
   ((not root) stack)
   ((assoc-pair? root) (cons (Assoc root) stack))
   ((collision-node? root) (cons (Collision (collision-node-entries root)) stack))
   (else (cons (Node root 0) stack))))

;; Returns two values: the next (key . value) association and the new
;; stack, or (values #f '()) when the stack is exhausted.
(define (pull-next stack)
  (if (null? stack)
      (values #f '())
      (let ((top (car stack)) (rest (cdr stack)))
	(cond
	 ((assoc-frame? top)
	  (values (assoc-frame-pair top) rest))
	 ((collision-frame? top)
	  (let ((entries (collision-frame-entries top)))
	    (values (car entries)
		    (if (null? (cdr entries))
			rest
			(cons (Collision (cdr entries)) rest)))))
	 (else
	  (let* ((node (node-frame-node top))
		 (slot (node-frame-slot top))
		 (datamap (bitmap-node-datamap node))
		 (nodemap (bitmap-node-nodemap node))
		 (array   (bitmap-node-array node))
		 (ndata   (fx* 2 (popcount32 datamap)))
		 (nnode   (popcount32 nodemap)))
	    (cond
	     ((fx< slot ndata)
	      (values (cons (vector-ref array slot) (vector-ref array (fx+ slot 1)))
		      (cons (Node node (fx+ slot 2)) rest)))
	     ((fx< (fx- slot ndata) nnode)
	      (let ((child (vector-ref array slot)))
		(pull-next (push-first child (cons (Node node (fx+ slot 1)) rest)))))
	     (else (pull-next rest)))))))))

(define-record-type <box>
  (make-box val)
  box?
  (val box-val box-val-set!))

(define (node-generator root project)
  (let ((b (make-box (push-first root '()))))
    (lambda ()
      (let-values (((item next-stack) (pull-next (box-val b))))
	(if (not item)
	    (eof-object)
	    (begin (box-val-set! b next-stack) (project item)))))))

(define (assoc-generator root) (node-generator root (lambda (item) item)))
(define (key-generator root)   (node-generator root car))
(define (value-generator root) (node-generator root cdr))

(define (tree-for-each-assoc root f)
  (let loop ((stack (push-first root '())))
    (let-values (((item next-stack) (pull-next stack)))
      (when item (f item) (loop next-stack)))))


;;
;; The champ-tree-map object
;;

(define (champ-tree-map key-hash key-equal #!key (new-root (Empty)))
  (let ((root new-root))
    (object
      ((persistent-unordered-map? self) #t)
      ((size self) (get-size root))

      ((empty? self) (not root))

      ((get self key)
       (or (find-assoc key-hash key-equal root key)
	   (apply-default-clause 'get key '())))

      ((get/default self key default-clause)
       (or (find-assoc key-hash key-equal root key)
	   (apply-default-clause 'get key (list default-clause))))

      ((get-value self key)
       (or (find-ref key-hash key-equal root key)
	   (apply-default-clause 'get-value key '())))

      ((get-value/default self key default-clause)
       (or (find-ref key-hash key-equal root key)
	   (apply-default-clause 'get-value key (list default-clause))))

      ((generate self p f g seed)
       (let recur ((new-root root) (seed seed))
	 (if (p seed)
	     (champ-tree-map key-hash key-equal new-root: new-root)
	     (let* ((item (f seed))
		    (new-root (insert key-hash key-equal (lambda (x ax) x) new-root (car item) (cdr item))))
	       (recur new-root (g seed))))))

      ((put self key value)
       (let ((new-root (insert key-hash key-equal (lambda (x ax) x) root key value)))
	 (champ-tree-map key-hash key-equal new-root: new-root)))

      ((update self key value merge-fn)
       (let ((new-root (insert key-hash key-equal merge-fn root key value)))
	 (champ-tree-map key-hash key-equal new-root: new-root)))

      ((delete self key)
       (let ((item+root (delete-assoc key-hash key-equal root key)))
	 (if item+root
	     (cons (car item+root)
		   (champ-tree-map key-hash key-equal new-root: (cdr item+root)))
	     (apply-default-clause 'delete key '()))))

      ((for-each-assoc self f) (tree-for-each-assoc root f))
      ((gen-assoc self) (assoc-generator root))

      ((map-root self) root)
      ((map-key-hash self) key-hash)
      ((map-key-equal self) key-equal)

      ;; collection behaviors
      ((collection? self) #t)
      ((gen-keys self) (key-generator root))
      ((gen-elts self) (value-generator root))
      ((for-each-key self proc)
       (tree-for-each-assoc root (lambda (item) (proc (car item)))))
      ((for-each-elt self proc)
       (tree-for-each-assoc root (lambda (item) (proc (cdr item)))))

      )))


;; A single, shared top-level procedure, not a fresh lambda built
;; inside champ-tree-map/equal on every call: union-with/withi/
;; transform require their two maps' key-hash procedures to be eq? to
;; each other, and two maps independently built via
;; champ-tree-map/equal must still satisfy that check.
(define (champ-tree-default-hash k) (hash k))

(define (champ-tree-map/equal #!key (new-root (Empty)))
  (champ-tree-map champ-tree-default-hash equal? new-root: new-root))


;;
;; Debug validity checker.  Returns #t iff ROOT satisfies every CHAMP
;; structural invariant: bitmap/array length and disjointness, hash-
;; chunk correctness along every path, canonical form (no non-root
;; node is a lone single-data-entry wrapper, no collision-node has
;; fewer than 2 entries), no node past +max-depth+, and no duplicate
;; keys anywhere in the whole trie.

(define (node-valid? key-hash key-equal node depth path-chunks is-root?)
  (cond
   ((not node) #t)
   ((assoc-pair? node) #t)
   ((collision-node? node)
    (let ((entries (collision-node-entries node)) (h (collision-node-hash node)))
      (and (>= (length entries) 2)
	   (every (lambda (kv) (fx= h (mask32 (key-hash (car kv))))) entries)
	   (every (lambda (kv) (fx= h (mask32 (key-hash (car kv)))))
		  entries)
	   ;; no duplicate keys within this collision-node
	   (let loop ((es entries))
	     (or (null? es)
		 (and (not (any (lambda (kv) (key-equal (car kv) (car (car es)))) (cdr es)))
		      (loop (cdr es))))))))
   ((bitmap-node? node)
    (and (fx<= depth +max-depth+)
	 (let* ((datamap (bitmap-node-datamap node))
		(nodemap (bitmap-node-nodemap node))
		(array   (bitmap-node-array node))
		(ndata   (popcount32 datamap))
		(nnode   (popcount32 nodemap)))
	   (and (fx= 0 (fxand datamap nodemap))
		(fx= (vector-length array) (fx+ (fx* 2 ndata) nnode))
		;; canonical form: a non-root node must not be a lone
		;; single-data-entry wrapper
		(or is-root? (not (and (fx= ndata 1) (fx= nnode 0))))
		;; every data entry's hash chunk at this depth matches
		;; the bit it is stored under
		(let dloop ((b 0) (di 0))
		  (cond
		   ((fx= b 32) #t)
		   ((bit-set? datamap b)
		    (let* ((k (vector-ref array di)))
		      (and (fx= b (hash-chunk (mask32 (key-hash k)) depth))
			   (dloop (fx+ b 1) (fx+ di 2)))))
		   (else (dloop (fx+ b 1) di))))
		;; every child's subtree is itself valid at depth+1
		(let nloop ((b 0) (ni (fx* 2 ndata)))
		  (cond
		   ((fx= b 32) #t)
		   ((bit-set? nodemap b)
		    (and (node-valid? key-hash key-equal (vector-ref array ni) (fx+ depth 1) path-chunks #f)
			 (nloop (fx+ b 1) (fx+ ni 1))))
		   (else (nloop (fx+ b 1) ni))))))))
   (else #f)))

(define (champ-tree-map-valid? m)
  (let ((root (map-root m)) (key-hash (map-key-hash m)) (key-equal (map-key-equal m)))
    (and (node-valid? key-hash key-equal root 0 '() #t)
	 ;; no duplicate keys anywhere in the whole trie
	 (let ((keys '()) (ok #t))
	   (tree-for-each-assoc root
	     (lambda (item)
	       (when (any (lambda (k) (key-equal k (car item))) keys) (set! ok #f))
	       (set! keys (cons (car item) keys))))
	   ok))))


;;
;; Structural map equality.  Two maps are equal iff they have the
;; same set of (key . value) associations (values compared with
;; equal?).  When both maps were built with the same key-hash/
;; key-equal procedures (checked by eq? on the stored procedures),
;; CHAMP's canonical form guarantees identical trie shape for
;; identical contents, so root equality decides it; otherwise a
;; linear fallback via GET is used.

(define (champ-tree-map-equal? m1 m2)
  (if (and (eq? (map-key-hash m1) (map-key-hash m2))
	   (eq? (map-key-equal m1) (map-key-equal m2)))
      (equal? (map-root m1) (map-root m2))
      (and (fx= (size m1) (size m2))
	   (let ((ok #t))
	     (for-each-assoc m1
	       (lambda (item)
		 (let ((other (get/default m2 (car item) #f)))
		   (unless (and other (equal? (cdr other) (cdr item))) (set! ok #f)))))
	     ok))))


;;
;; Union family
;;
;; Unions of maps.  Each union takes two maps M1 and M2, created by
;; champ-tree-map with key-hash/key-equal procedures that agree with
;; each other (checked by eq? on the stored procedures, since a
;; mismatch would silently corrupt structure rather than merely
;; disorder results the way a key-compare mismatch would in rb-tree),
;; and returns a new map whose domain is the union of their domains.
;; The new map uses the key-hash/key-equal of M1.  The inputs are not
;; modified.
;;
;;  ((union-with MERGE-FN) M1 M2)
;;
;;	MERGE-FN :: x y -> value defines the value of a key that is
;;	in both maps, where x is its value in M1 and y its value in M2.
;;
;;  ((union-withi MERGE-FN) M1 M2)
;;
;;	as union-with, but MERGE-FN :: key x y -> value also receives
;;	the key.
;;
;;  ((union-transform FN MERGE-FN) M1 M2)
;;
;;	maps the value of every key in only one map through FN :: x ->
;;	value, and the value of every key in both maps through
;;	MERGE-FN :: x y -> value.  Returns a list (N M KT1 KT2), where
;;	N is the number of keys in the new map M, KT1 is a list of (x
;;	. value) pairs that relates each value x in M1 to its new value
;;	in M, and KT2 is the corresponding list for M2.  A key in both
;;	maps contributes a pair to both KT1 and KT2.  Unlike rb-tree's
;;	union-transform, KT1/KT2's order is NOT guaranteed ascending by
;;	key -- there is no key order in a hash map.  The order is
;;	unspecified relative to key values, but deterministic for a
;;	given pair of input maps and a given key-hash function, since
;;	the underlying trie merge visits bits in a fixed order at every
;;	level.

;; Returns a node structurally identical to NODE but with every value
;; replaced by (transform key value).  Used for the "one side of the
;; union is absent here" base case: every surviving entry still
;; passes through on-left or on-right, even though there is nothing
;; on the other side to merge against.
(define (clone-node-values transform node)
  (cond
   ((not node) #f)
   ((collision-node? node)
    (CollisionNode (collision-node-hash node)
		   (map (lambda (kv) (cons (car kv) (transform (car kv) (cdr kv))))
			(collision-node-entries node))))
   (else
    (let* ((datamap (bitmap-node-datamap node))
	   (nodemap (bitmap-node-nodemap node))
	   (array   (bitmap-node-array node))
	   (ndata   (popcount32 datamap))
	   (nnode   (popcount32 nodemap))
	   (new-array (vector-copy array)))
      (do ((i 0 (fx+ i 1))) ((fx= i ndata))
	(vector-set! new-array (fx+ (fx* 2 i) 1)
		     (transform (vector-ref array (fx* 2 i)) (vector-ref array (fx+ (fx* 2 i) 1)))))
      (do ((i 0 (fx+ i 1))) ((fx= i nnode))
	(vector-set! new-array (fx+ (fx* 2 ndata) i)
		     (clone-node-values transform (vector-ref array (fx+ (fx* 2 ndata) i)))))
      (BitmapNode datamap nodemap new-array)))))


;; Merges two bitmap-nodes bit by bit.  Every one of the 3x3 = 9
;; (Absent/Data/Child) x (Absent/Data/Child) combinations is handled
;; explicitly, falling through to an internal-error assertion for the
;; impossible remainder.  Note that union never shrinks a subtree
;; below the entry count of its larger input (on-left/on-right always
;; pass every unique key through, on-both still produces one entry
;; per overlapping key), so unlike delete, no canonicalization step is
;; needed here: a child merge result can never collapse to a
;; single-entry shape when both of its contributing sides already
;; satisfy the non-root canonical-form invariant (each has >= 2
;; entries, or is a collision-node with >= 2 entries).
(define (merge-bitmaps key-hash key-equal on-left on-right on-both n1 n2 depth)
  (let ((d1 (bitmap-node-datamap n1)) (m1 (bitmap-node-nodemap n1)) (a1 (bitmap-node-array n1))
	(d2 (bitmap-node-datamap n2)) (m2 (bitmap-node-nodemap n2)) (a2 (bitmap-node-array n2)))
    (let loop ((b 0) (new-datamap 0) (new-nodemap 0) (data-pairs '()) (nodes '()))
      (if (fx= b 32)
	  (BitmapNode new-datamap new-nodemap
		      (vector-append
		       (list->vector (apply append (map (lambda (p) (list (car p) (cdr p)))
							 (reverse data-pairs))))
		       (list->vector (reverse nodes))))
	  (let* ((d1b (bit-set? d1 b)) (n1b (bit-set? m1 b))
		 (d2b (bit-set? d2 b)) (n2b (bit-set? m2 b)))
	    (cond
	     ((and (not d1b) (not n1b) (not d2b) (not n2b))
	      (loop (fx+ b 1) new-datamap new-nodemap data-pairs nodes))
	     ((and d1b (not d2b) (not n2b))
	      (let* ((di (data-index d1 b)) (k (vector-ref a1 di)) (v (vector-ref a1 (fx+ di 1))))
		(loop (fx+ b 1) (fxior new-datamap (fxshl 1 b)) new-nodemap
		      (cons (cons k (on-left k v)) data-pairs) nodes)))
	     ((and d2b (not d1b) (not n1b))
	      (let* ((di (data-index d2 b)) (k (vector-ref a2 di)) (v (vector-ref a2 (fx+ di 1))))
		(loop (fx+ b 1) (fxior new-datamap (fxshl 1 b)) new-nodemap
		      (cons (cons k (on-right k v)) data-pairs) nodes)))
	     ((and n1b (not d2b) (not n2b))
	      (let ((c (vector-ref a1 (node-index d1 m1 b))))
		(loop (fx+ b 1) new-datamap (fxior new-nodemap (fxshl 1 b)) data-pairs
		      (cons (clone-node-values on-left c) nodes))))
	     ((and n2b (not d1b) (not n1b))
	      (let ((c (vector-ref a2 (node-index d2 m2 b))))
		(loop (fx+ b 1) new-datamap (fxior new-nodemap (fxshl 1 b)) data-pairs
		      (cons (clone-node-values on-right c) nodes))))
	     ((and d1b d2b)
	      (let* ((di1 (data-index d1 b)) (k1 (vector-ref a1 di1)) (v1 (vector-ref a1 (fx+ di1 1)))
		     (di2 (data-index d2 b)) (k2 (vector-ref a2 di2)) (v2 (vector-ref a2 (fx+ di2 1))))
		(if (key-equal k1 k2)
		    (loop (fx+ b 1) (fxior new-datamap (fxshl 1 b)) new-nodemap
			  (cons (cons k1 (on-both k1 v1 v2)) data-pairs) nodes)
		    (loop (fx+ b 1) new-datamap (fxior new-nodemap (fxshl 1 b)) data-pairs
			  (cons (two-entry-node (fx+ depth 1)
						 (mask32 (key-hash k1)) k1 (on-left k1 v1)
						 (mask32 (key-hash k2)) k2 (on-right k2 v2))
				nodes)))))
	     ((and n1b n2b)
	      (let ((c1 (vector-ref a1 (node-index d1 m1 b))) (c2 (vector-ref a2 (node-index d2 m2 b))))
		(loop (fx+ b 1) new-datamap (fxior new-nodemap (fxshl 1 b)) data-pairs
		      (cons (merge-node key-hash key-equal on-left on-right on-both c1 c2 (fx+ depth 1))
			    nodes))))
	     ((and d1b n2b)
	      (let* ((di (data-index d1 b)) (k (vector-ref a1 di)) (v (vector-ref a1 (fx+ di 1)))
		     (c (vector-ref a2 (node-index d2 m2 b))))
		(loop (fx+ b 1) new-datamap (fxior new-nodemap (fxshl 1 b)) data-pairs
		      (cons (node-insert key-hash key-equal
					 (lambda (kk vv) (on-left kk vv))
					 (lambda (kk newv oldv) (on-both kk newv oldv))
					 c (fx+ depth 1) (mask32 (key-hash k)) k v)
			    nodes))))
	     ((and n1b d2b)
	      (let* ((di (data-index d2 b)) (k (vector-ref a2 di)) (v (vector-ref a2 (fx+ di 1)))
		     (c (vector-ref a1 (node-index d1 m1 b))))
		(loop (fx+ b 1) new-datamap (fxior new-nodemap (fxshl 1 b)) data-pairs
		      (cons (node-insert key-hash key-equal
					 (lambda (kk vv) (on-right kk vv))
					 (lambda (kk newv oldv) (on-both kk oldv newv))
					 c (fx+ depth 1) (mask32 (key-hash k)) k v)
			    nodes))))
	     (else (champ-tree:error 'merge-node "impossible bit classification"))))))))


;; Flattens a real trie node (bitmap-node or collision-node) to its
;; full list of (key . value) associations.
(define (node->entries node) (reverse (let ((acc '())) (tree-for-each-assoc node (lambda (item) (set! acc (cons item acc)))) acc)))

;; Merges two association lists by key-equal.  Every key unique to XS
;; passes through ON-LEFT, every key unique to YS passes through
;; ON-RIGHT, every key in both passes through ON-BOTH (key x y).
;; Collision lists are expected to stay small (true full-hash
;; collisions are rare), so the straightforward O(|xs|*|ys|) scan here
;; is an acceptable, simple, and clearly-correct choice.
(define (alist-merge key-equal on-left on-right on-both xs ys)
  (let* ((ys-only (let loop ((ys ys) (acc '()))
		    (cond
		     ((null? ys) acc)
		     ((any (lambda (x) (key-equal (car x) (car (car ys)))) xs) (loop (cdr ys) acc))
		     (else (loop (cdr ys) (cons (car ys) acc))))))
	 (left+both (map (lambda (x)
			    (let ((match (assoc (car x) ys key-equal)))
			      (if match
				  (cons (car x) (on-both (car x) (cdr x) (cdr match)))
				  (cons (car x) (on-left (car x) (cdr x))))))
			  xs))
	 (right (map (lambda (y) (cons (car y) (on-right (car y) (cdr y)))) ys-only)))
    (append left+both right)))

;; Rebuilds a trie subtree rooted at DEPTH from a flat list of
;; (key . value) pairs with pairwise-distinct keys and length >= 2
;; (the only case this is used for -- see merge-node's collision
;; cases below).  Never produces the bare-pair singleton shape, which
;; is reserved for the whole map's root.
(define (build-node-from-entries key-hash key-equal entries depth)
  (let* ((e0 (car entries)) (e1 (cadr entries))
	 (seed (two-entry-node depth
			       (mask32 (key-hash (car e0))) (car e0) (cdr e0)
			       (mask32 (key-hash (car e1))) (car e1) (cdr e1))))
    (let loop ((es (cddr entries)) (node seed))
      (if (null? es)
	  node
	  (let* ((kv (car es)) (h (mask32 (key-hash (car kv)))))
	    (loop (cdr es)
		  (node-insert key-hash key-equal (lambda (k v) v) (lambda (k new old) new)
			       node depth h (car kv) (cdr kv))))))))

;; Merges two real trie nodes (never #f, never a bare pair -- children
;; are always real nodes, see the node-representation comment above).
;; The common bitmap-vs-bitmap case is handled structurally by
;; merge-bitmaps; any case touching a collision-node is resolved by
;; flattening both sides to entry lists and rebuilding, since
;; collision-nodes are rare and the two-bitmap structural alignment
;; merge-bitmaps relies on does not apply once a hash is fully
;; exhausted.
(define (merge-node key-hash key-equal on-left on-right on-both n1 n2 depth)
  (cond
   ((and (bitmap-node? n1) (bitmap-node? n2))
    (merge-bitmaps key-hash key-equal on-left on-right on-both n1 n2 depth))
   (else
    (let ((merged (alist-merge key-equal on-left on-right on-both (node->entries n1) (node->entries n2))))
      (build-node-from-entries key-hash key-equal merged depth)))))


;; Top-level union, handling the three root shapes on both sides.
(define (merge-roots key-hash key-equal on-left on-right on-both root1 root2)
  (cond
   ((and (not root1) (not root2)) #f)
   ((not root1)
    (if (assoc-pair? root2)
	(cons (car root2) (on-right (car root2) (cdr root2)))
	(clone-node-values on-right root2)))
   ((not root2)
    (if (assoc-pair? root1)
	(cons (car root1) (on-left (car root1) (cdr root1)))
	(clone-node-values on-left root1)))
   ((and (assoc-pair? root1) (assoc-pair? root2))
    (if (key-equal (car root1) (car root2))
	(cons (car root1) (on-both (car root1) (cdr root1) (cdr root2)))
	(two-entry-node 0
			 (mask32 (key-hash (car root1))) (car root1) (on-left (car root1) (cdr root1))
			 (mask32 (key-hash (car root2))) (car root2) (on-right (car root2) (cdr root2)))))
   ((assoc-pair? root1)
    (node-insert key-hash key-equal
		 (lambda (k v) (on-left k v))
		 (lambda (k new old) (on-both k new old))
		 root2 0 (mask32 (key-hash (car root1))) (car root1) (cdr root1)))
   ((assoc-pair? root2)
    (node-insert key-hash key-equal
		 (lambda (k v) (on-right k v))
		 (lambda (k new old) (on-both k old new))
		 root1 0 (mask32 (key-hash (car root2))) (car root2) (cdr root2)))
   (else (merge-node key-hash key-equal on-left on-right on-both root1 root2 0))))


(define (check-compatible m1 m2)
  (unless (and (eq? (map-key-hash m1) (map-key-hash m2))
	       (eq? (map-key-equal m1) (map-key-equal m2)))
    (champ-tree:error 'union "maps do not share the same key-hash/key-equal procedures")))

(define (union-with merge-fn)
  (lambda (m1 m2)
    (check-compatible m1 m2)
    (champ-tree-map (map-key-hash m1) (map-key-equal m1)
		     new-root: (merge-roots (map-key-hash m1) (map-key-equal m1)
					     (lambda (k x) x) (lambda (k y) y)
					     (lambda (k x y) (merge-fn x y))
					     (map-root m1) (map-root m2)))))

(define (union-withi merge-fn)
  (lambda (m1 m2)
    (check-compatible m1 m2)
    (champ-tree-map (map-key-hash m1) (map-key-equal m1)
		     new-root: (merge-roots (map-key-hash m1) (map-key-equal m1)
					     (lambda (k x) x) (lambda (k y) y)
					     merge-fn
					     (map-root m1) (map-root m2)))))

(define (union-transform fn merge-fn)
  (lambda (m1 m2)
    (check-compatible m1 m2)
    (let ((n 0) (kt1 '()) (kt2 '()))
      (let ((root (merge-roots (map-key-hash m1) (map-key-equal m1)
				(lambda (k x)
				  (let ((x1 (fn x)))
				    (set! n (fx+ 1 n))
				    (set! kt1 (cons (cons x x1) kt1))
				    x1))
				(lambda (k y)
				  (let ((y1 (fn y)))
				    (set! n (fx+ 1 n))
				    (set! kt2 (cons (cons y y1) kt2))
				    y1))
				(lambda (k x y)
				  (let ((v (merge-fn x y)))
				    (set! n (fx+ 1 n))
				    (set! kt1 (cons (cons x v) kt1))
				    (set! kt2 (cons (cons y v) kt2))
				    v))
				(map-root m1) (map-root m2))))
	(list n (champ-tree-map (map-key-hash m1) (map-key-equal m1) new-root: root)
	      (reverse kt1) (reverse kt2))))))

)
