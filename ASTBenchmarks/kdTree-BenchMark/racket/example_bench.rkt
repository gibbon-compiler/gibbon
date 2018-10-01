#lang racket
;; We get to use the full Racket language here.

;; We import the code from the more restricted language: 
(require "example_traverse.gib") ;; just test garbage
(require "traversal.gib")

(display "Here's a data value, from treelang, but allocated in Racket code:\n" )
(write (Foo 3))

(newline)

;; build-tree can use the full Racket language.
;; In fact, this code is not type checked.
(define (build-tree sz)
  (Bar (Foo 3) (Foo 1)))

(define (bench sz iters)
  (define tr (build-tree sz))
  ;; Use the traversal written in treelang
  (time
   (for ((_ (in-range iters)))
     (traverse tr))))

(bench 20 10)
(display "Done benchmarking\n")
