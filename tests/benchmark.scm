;;
;; Informal performance benchmark for champ-tree.
;;
;; Not part of the `test`-egg suite; run directly with
;; `csi -s tests/benchmark.scm` (or compiled) to get a feel for
;; CHAMP's near-O(1) put/get/delete/union behavior at scale, for
;; comparison against rb-tree's own tests/benchmark.scm at
;; comparable sizes.

(import scheme (chicken base) (chicken fixnum) (srfi 69) champ-tree yasos-collections)

(define (++ x) (fx+ 1 x))

(define min-key 1)
(define max-key 1000000)

(define (new-map) (champ-tree-map/equal))

(define (compute-assoc key) (cons key (++ key)))

(display "building a map of ") (display max-key) (display " associations:") (newline)
(define m
  (time
   (let recur ((m (new-map)) (i min-key))
     (let ((m1 (put m i (cdr (compute-assoc i)))))
       (if (< i max-key) (recur m1 (++ i)) m1)))))

(display "size: ") (display (size m)) (newline)

(display "looking up every key once:") (newline)
(time
 (let loop ((i min-key))
   (when (<= i max-key)
     (get-value m i)
     (loop (++ i)))))

(display "deleting every key:") (newline)
(define emptied
  (time
   (let recur ((m m) (i min-key))
     (if (> i max-key)
	 m
	 (recur (cdr (delete m i)) (++ i))))))
(display "size after deleting all: ") (display (size emptied)) (newline)

(display "building two maps of ") (display (quotient max-key 2)) (display " associations each, for union:") (newline)
(define m1 (let recur ((m (new-map)) (i min-key)) (if (> i (quotient max-key 2)) m (recur (put m i i) (++ i)))))
(define m2 (let recur ((m (new-map)) (i (quotient max-key 4)))
	     (if (> i (+ (quotient max-key 4) (quotient max-key 2))) m (recur (put m i i) (++ i)))))

(display "union-with:") (newline)
(define u (time ((union-with (lambda (x y) x)) m1 m2)))
(display "union size: ") (display (size u)) (newline)
