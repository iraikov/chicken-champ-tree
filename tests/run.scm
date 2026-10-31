
;;
;; Verifying the champ-tree package
;;

(import scheme (chicken base) (chicken format) (prefix (chicken sort) s:)
	srfi-1 (srfi 69) champ-tree yasos-collections test)

(define (generator->list g)
  (let loop ((ax '()))
    (let ((x (g)))
      (if (eof-object? x) (reverse ax) (loop (cons x ax))))))

(define (++ x) (+ 1 x))
(define (-- x) (- x 1))

(define min-key 1)
(define max-key 10000)

(define (new-map) (champ-tree-map/equal))

;; a hard-wired association between a key and a value
(define compute-assoc (lambda (key) (cons key (++ key))))

;; alists/sets have no key order, so every comparison against a model
;; goes through set-equality on (key . value) pairs rather than
;; equal? on an ordered list, unlike rb-tree's tests.
(define (alist-set-equal? a b)
  (and (= (length a) (length b))
       (every (lambda (kv) (member kv b)) a)
       (every (lambda (kv) (member kv a)) b)))

(define (sort-alist l) (s:sort l (lambda (a b) (< (car a) (car b)))))

(test-group "persistent unordered map"

  (test-group "the empty and size predicates on an empty map"
    (let ((m (new-map)))
      (test-assert (empty? m))
      (test-assert (zero? (size m)))
      (test-assert (persistent-unordered-map? m))))

  (test-group (sprintf "loading a sequence [~A,~A]" min-key max-key)
    (let ((m (new-map)))
      (let ((m1
	     (time
	      (let recur ((m m) (i min-key))
		(let ((m1 (put m i (cdr (compute-assoc i)))))
		  (test (sprintf "get element ~A" i) (compute-assoc i) (get m1 i))
		  (if (< i max-key) (recur m1 (++ i)) m1))))))

	(test (++ (- max-key min-key)) (size m1))
	(test-assert (not (empty? m1)))

	(test (compute-assoc (++ min-key)) (get m1 (++ min-key)))
	(test (compute-assoc (++ min-key)) (get/default m1 (++ min-key) #f))

	(test-assert "looking up of non-existing keys"
		     (not (get/default m1 (-- min-key) #f))))))

  (test-group (sprintf "generating a sequence [~A,~A]" min-key max-key)
    (let ((m (new-map)))
      (let ((m1
	     (time
	      (generate m (lambda (x) (> x max-key))
			(lambda (x) (compute-assoc x))
			(lambda (x) (++ x))
			min-key))))

	(test (++ (- max-key min-key)) (size m1))
	(test-assert (not (empty? m1)))

	(test (compute-assoc (++ min-key)) (get m1 (++ min-key)))
	(test (compute-assoc (++ min-key)) (get/default m1 (++ min-key) #f)))))

  (test-group "reloading the same sequence and then deleting"
    (let ((m (new-map)))
      (let ((m1
	     (time
	      (let recur ((m m) (i max-key))
		(let ((m1 (put m i (cdr (compute-assoc i)))))
		  (test (sprintf "get element ~A" i) (compute-assoc i) (get m1 i))
		  (let ((m2 (delete m1 i)))
		    (if (< min-key i) (recur (cdr m2) (- i 1)) (cdr m2))))))))
	(test-assert (zero? (size m1))))))

  (test-group "reduce and map via yasos-collections"
    (let ((m
	   (let recur ((m (new-map)) (i min-key))
	     (let ((m1 (put m i (cdr (compute-assoc i)))))
	       (if (< i max-key) (recur m1 (++ i)) m1)))))

      (test "using reduce to sum the elements in the persistent-map"
	    (* 5000 (+ (+ 1 min-key) (+ 1 max-key)))
	    (reduce (lambda (x sum) (+ x sum)) 0 m))))

  (test-group "unordered-traversal operations on an empty map"
    (let ((m (new-map)))
      (test '() (let ((acc '())) (for-each-assoc m (lambda (kv) (set! acc (cons kv acc)))) acc))
      (test '() (generator->list (gen-assoc m)))
      (test '() (generator->list (gen-keys m)))
      (test '() (generator->list (gen-elts m)))))

  (test-group "unordered-traversal operations and their repeatability"
    (let ((m (fold (lambda (k m) (put m k (++ k))) (new-map) '(5 3 9 1 7 2 8))))
      (define expected (map compute-assoc '(5 3 9 1 7 2 8)))
      (test-assert "for-each-assoc visits every association"
		   (alist-set-equal? expected
				      (let ((acc '())) (for-each-assoc m (lambda (kv) (set! acc (cons kv acc)))) acc)))
      (test-assert "gen-assoc matches for-each-assoc"
		   (equal? (let ((acc '())) (for-each-assoc m (lambda (kv) (set! acc (cons kv acc)))) (reverse acc))
			   (generator->list (gen-assoc m))))
      ;; traversal order is unspecified relative to keys, but
      ;; deterministic for a given final set of associations --
      ;; re-traversing the same map, and a differently-built map with
      ;; the same contents, must both yield the identical order.
      (define order1 (generator->list (gen-assoc m)))
      (define order2 (generator->list (gen-assoc m)))
      (test-assert "repeated traversal of the same map is order-identical" (equal? order1 order2))
      (define m-rebuilt (fold (lambda (k m) (put m k (++ k))) (new-map) '(1 2 3 5 7 8 9)))
      (test-assert "differently-ordered build of the same contents matches traversal order"
		   (equal? order1 (generator->list (gen-assoc m-rebuilt))))))

  (test-group "random puts and deletes against a plain alist model"
    (define (next-seed s) (modulo (+ (* s 1103515245) 12345) 2147483648))
    (define (model-put lst k v) (cons (cons k v) (remove (lambda (p) (eqv? (car p) k)) lst)))
    (define (model-delete lst k) (remove (lambda (p) (eqv? (car p) k)) lst))
    (define (check nsteps nkeys hash-fn)
      (let loop ((i 0) (s 7) (m (champ-tree-map hash-fn eqv?)) (model '()) (ok #t))
	(if (or (= i nsteps) (not ok))
	    (begin (unless ok (printf "mismatch at step ~A~%" i)) ok)
	    (let* ((s (next-seed s))
		   (k (modulo (quotient s 7) nkeys)))
	      (receive (m model)
		  (cond ((even? (quotient s 3))
			 (values (put m k (* 10 k)) (model-put model k (* 10 k))))
			((assv k model)
			 (values (cdr (delete m k)) (model-delete model k)))
			(else (values m model)))
		(loop (+ i 1) s m model
		      (and (= (length model) (size m))
			   (champ-tree-map-valid? m)
			   (every (lambda (p) (equal? (cdr p) (get-value m (car p)))) model))))))))
    (test-assert "2000 steps over keys 0-39, equal?-based hash" (check 2000 40 (lambda (k) (hash k))))
    (test-assert "5000 steps over keys 0-299, equal?-based hash" (check 5000 300 (lambda (k) (hash k))))
    (test-assert "2000 steps over keys 0-39, collision-heavy hash (mod 4)" (check 2000 40 (lambda (k) (modulo k 4))))
    (test-assert "2000 steps over keys 0-39, always-colliding hash" (check 2000 40 (lambda (k) 0))))

  (test-group "canonical form and structural map equality"
    (define (alist->map alist) (fold (lambda (kv m) (put m (car kv) (cdr kv))) (new-map) alist))
    (define low (map (lambda (k) (cons k k)) (iota 30 0)))
    (test-assert "same map equal to itself" (champ-tree-map-equal? (alist->map low) (alist->map low)))
    (test-assert "same contents, forward build order, equal"
		 (champ-tree-map-equal? (alist->map low) (alist->map (reverse low))))
    (test-assert "same contents, random build order, equal"
		 (champ-tree-map-equal? (alist->map low) (alist->map (s:sort low (lambda (a b) (odd? (+ (car a) (car b)))) ))))
    (test-assert "different contents, not equal"
		 (not (champ-tree-map-equal? (alist->map low) (alist->map (cons (cons 1000 1000) low)))))
    ;; build the same final contents via two different sequences of
    ;; put/delete and confirm the maps are not just behaviorally equal
    ;; but (via the fast canonical-form path) literally structurally
    ;; identical from the outside, i.e. all operations agree.
    (let* ((a (put (put (put (new-map) 1 'a) 2 'b) 3 'c))
	   (b (cdr (delete (put (put (put (put (new-map) 9 'z) 1 'a) 2 'b) 3 'c) 9))))
      (test-assert "two different build/delete histories, same contents, equal" (champ-tree-map-equal? a b))))

  (test-group "node-collapse on delete (canonicalization)"
    ;; with a collision-heavy hash, deleting one of two collision-node
    ;; entries must leave a canonical map (champ-tree-map-valid?),
    ;; deleting a bitmap-node sub-entry down to one remaining
    ;; association anywhere in the map must do the same.
    (define (collide4 k) (modulo k 4))
    (let* ((m (fold (lambda (k m) (put m k k)) (champ-tree-map collide4 eqv?) (iota 20 0)))
	   (after-one-delete (cdr (delete m 0))))
      (test-assert "valid after deleting one of many colliding entries" (champ-tree-map-valid? after-one-delete))
      (test (- (size m) 1) (size after-one-delete)))
    (let* ((m (put (put (champ-tree-map collide4 eqv?) 0 'a) 4 'b))
	   (after (cdr (delete m 4))))
      (test-assert "valid after collapsing a 2-entry collision-node to 1" (champ-tree-map-valid? after))
      (test 1 (size after))
      (test 'a (get-value after 0))))

  (test-group "negative test: a non-deterministic hash is caught as invalid"
    ;; champ-tree-map-valid? checks that every data entry's recorded
    ;; position matches a fresh re-computation of its hash chunks;
    ;; a hash function that answers differently for the same key on a
    ;; later call (an internal-consistency violation no honest caller
    ;; should ever trigger) must therefore be flagged.
    (define calls 0)
    (define (unstable-hash k)
      (set! calls (+ calls 1))
      (if (<= calls 3) 0 999999))
    (let ((m (put (put (put (champ-tree-map unstable-hash eqv?) 1 'a) 2 'b) 3 'c)))
      (test-assert "unstable hash produces a map flagged invalid" (not (champ-tree-map-valid? m)))))

  (test-group "unions"
    (define (alist->map alist) (fold (lambda (kv m) (put m (car kv) (cdr kv))) (new-map) alist))
    (define (map->alist m) (let ((acc '())) (for-each-assoc m (lambda (kv) (set! acc (cons kv acc)))) acc))
    (define (check-map name expected m)
      (test-assert (string-append name ": associations") (alist-set-equal? expected (map->alist m)))
      (test (string-append name ": size") (length expected) (size m))
      (test-assert (string-append name ": CHAMP invariants") (champ-tree-map-valid? m)))

    (define odds  (map (lambda (k) (cons k (* 10 k))) (iota 20 1 2)))
    (define evens (map (lambda (k) (cons k (* 10 k))) (iota 20 0 2)))
    (define low   (map (lambda (k) (cons k k)) (iota 10 0)))
    (define mid   (map (lambda (k) (cons k (- k))) (iota 10 5)))

    (test-group "union-with"
      (check-map "disjoint" (append odds evens) ((union-with +) (alist->map odds) (alist->map evens)))
      (check-map "overlapping"
		 (append (map (lambda (k) (cons k k)) (iota 5 0))
			 (map (lambda (k) (cons k 0)) (iota 5 5))
			 (map (lambda (k) (cons k (- k))) (iota 5 10)))
		 ((union-with +) (alist->map low) (alist->map mid)))
      (check-map "empty left" mid ((union-with +) (new-map) (alist->map mid)))
      (check-map "empty right" low ((union-with +) (alist->map low) (new-map)))
      (check-map "both empty" '() ((union-with +) (new-map) (new-map)))
      (check-map "identical (self-union)" (map (lambda (kv) (cons (car kv) (* 2 (cdr kv)))) low)
		 ((union-with +) (alist->map low) (alist->map low)))
      (let* ((m1 (alist->map low)) (m2 (alist->map mid))
	     (u ((union-with +) m1 m2)))
	(test-assert "inputs unchanged" (and (alist-set-equal? low (map->alist m1))
					      (alist-set-equal? mid (map->alist m2))))
	(test "result supports put" (cons 100 1) (get (put u 100 1) 100))
	(test "result supports delete" 14 (size (cdr (delete u 7))))))

    (test-group "union-withi"
      (check-map "overlapping"
		 (append (map (lambda (k) (cons k k)) (iota 5 0))
			 (map (lambda (k) (cons k (list k k (- k)))) (iota 5 5))
			 (map (lambda (k) (cons k (- k))) (iota 5 10)))
		 ((union-withi list) (alist->map low) (alist->map mid)))
      (check-map "disjoint" (append odds evens) ((union-withi list) (alist->map odds) (alist->map evens)))
      (check-map "empty left" low ((union-withi list) (new-map) (alist->map low))))

    (test-group "union-transform"
      ;; FN/MERGE-FN assign sequential counter positions (0, 1, 2, ...)
      ;; as they are called, the same way rb-tree's own test models a
      ;; dataframe-merge; but unlike rb-tree, that call order follows
      ;; the trie's own layout, not ascending key order, so the exact
      ;; (key . counter-value) mapping is not predictable from the
      ;; inputs alone.  Every other property is: N, the final map's
      ;; key set and size, and KT1/KT2's internal consistency with the
      ;; final map and the original inputs.  check-union-transform
      ;; verifies all of those without assuming any particular order.
      (define (run alist1 alist2)
	(let ((counter 0))
	  ((union-transform
	    (lambda (x) (let ((c counter)) (set! counter (+ 1 c)) c))
	    (lambda (x y) (let ((c counter)) (set! counter (+ 1 c)) c)))
	   (alist->map alist1) (alist->map alist2))))
      ;; NOTE: the facts this check needs are deliberately computed in
      ;; a separate helper (union-transform-facts), rather than inline
      ;; via a multi-binding let* at the test-call site -- the `test`
      ;; egg's macro mishandles `test`/`test-assert` forms nested more
      ;; than a few `let` levels deep (observed directly: it signals
      ;; "the test expression should come last" once 5 or more
      ;; sequential let* bindings precede the test call, regardless of
      ;; what those bindings compute), so every test call here sits
      ;; under a single `let` binding one pre-computed facts list.
      (define (union-transform-facts alist1 alist2 result)
	(let* ((n (list-ref result 0)) (m (list-ref result 1))
	       (kt1 (list-ref result 2)) (kt2 (list-ref result 3))
	       (keys1 (map car alist1)) (keys2 (map car alist2))
	       (all-keys (delete-duplicates (append keys1 keys2)))
	       (map-keys (map car (let ((acc '())) (for-each-assoc m (lambda (kv) (set! acc (cons kv acc)))) acc)))
	       (kt1-consistent (every (lambda (kv) (let ((v (assv (car kv) alist1)))
						      (equal? (cdr (assoc (cdr v) kt1)) (get-value m (car kv)))))
				       alist1))
	       (kt2-consistent (every (lambda (kv) (let ((v (assv (car kv) alist2)))
						      (equal? (cdr (assoc (cdr v) kt2)) (get-value m (car kv)))))
				       alist2)))
	  (list n m kt1 kt2 all-keys map-keys kt1-consistent kt2-consistent)))
      (define (check-union-transform name alist1 alist2 result)
	(let ((f (union-transform-facts alist1 alist2 result)))
	  (test (string-append name ": n") (length (list-ref f 4)) (list-ref f 0))
	  (test-assert (string-append name ": CHAMP invariants") (champ-tree-map-valid? (list-ref f 1)))
	  (test-assert (string-append name ": map keys") (lset= eqv? (list-ref f 4) (list-ref f 5)))
	  (test (string-append name ": kt1 length") (length alist1) (length (list-ref f 2)))
	  (test (string-append name ": kt2 length") (length alist2) (length (list-ref f 3)))
	  (test-assert (string-append name ": kt1 consistent with final map") (list-ref f 6))
	  (test-assert (string-append name ": kt2 consistent with final map") (list-ref f 7))))
      (define pos1 (map (lambda (k i) (cons k i)) '(1 3 5 7) (iota 4)))
      (define pos2 (map (lambda (k i) (cons k i)) '(3 4 7 9 10) (iota 5 100)))

      (check-union-transform "overlapping" pos1 pos2 (run pos1 pos2))
      (check-union-transform "empty right" pos1 '() (run pos1 '()))
      (check-union-transform "empty left" '() pos2 (run '() pos2))
      (check-union-transform "both empty" '() '() (run '() '()))
      (check-union-transform "disjoint"
			      (map (lambda (k) (cons k k)) (iota 10 0 2))
			      (map (lambda (k) (cons k k)) (iota 10 1 2))
			      (run (map (lambda (k) (cons k k)) (iota 10 0 2))
				   (map (lambda (k) (cons k k)) (iota 10 1 2))))

      ;; running the identical union twice must produce identical
      ;; kt1/kt2 order -- unspecified relative to key order, but
      ;; deterministic for a given pair of input maps.
      (let ((r1 (run pos1 pos2)) (r2 (run pos1 pos2)))
	(test-assert "kt1 order is repeatable across identical unions" (equal? (list-ref r1 2) (list-ref r2 2)))
	(test-assert "kt2 order is repeatable across identical unions" (equal? (list-ref r1 3) (list-ref r2 3)))))

    (test-group "mismatched key-hash/key-equal procedures error"
      (test-error ((union-with +) (champ-tree-map (lambda (k) k) eqv?) (champ-tree-map (lambda (k) k) eqv?))))

    (test-group "unions involving collision-nodes"
      (define (collide0 k) 0)
      (define coll-a (fold (lambda (k m) (put m k (* k k))) (champ-tree-map collide0 eqv?) '(1 2 3)))
      (define coll-b (fold (lambda (k m) (put m k (* k k))) (champ-tree-map collide0 eqv?) '(4 5)))
      (check-map "always-colliding union" (map (lambda (k) (cons k (* k k))) '(1 2 3 4 5))
		 ((union-with (lambda (x y) x)) coll-a coll-b))
      (define (collide4 k) (modulo k 4))
      (define split-a (fold (lambda (k m) (put m k k)) (champ-tree-map collide4 eqv?) '(0 1 2 3)))
      (define split-b (fold (lambda (k m) (put m k k)) (champ-tree-map collide4 eqv?) '(4 5 6 7)))
      (check-map "collision-heavy union across chunk boundaries"
		 (map (lambda (k) (cons k k)) '(0 1 2 3 4 5 6 7))
		 ((union-with (lambda (x y) x)) split-a split-b)))

    (test-group "large unions keep the CHAMP invariants"
      (for-each
       (lambda (n1 n2)
	 (let* ((a1 (map (lambda (k) (cons k k)) (iota n1 0 3)))
		(a2 (map (lambda (k) (cons k k)) (iota n2 0 2)))
		(u ((union-with (lambda (x y) x)) (alist->map a1) (alist->map a2)))
		(keys (delete-duplicates (append (map car a1) (map car a2)))))
	   (test-assert (sprintf "union of ~A and ~A keys" n1 n2)
			(lset= eqv? keys (map car (map->alist u))))
	   (test-assert (sprintf "invariants for ~A and ~A keys" n1 n2) (champ-tree-map-valid? u))))
       '(1 2 3 7 100 1000 1 0)
       '(1 1 5 8 333 1    1000 1023)))))

(test-exit)
