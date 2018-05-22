#lang gibbon

;; This is an example of the binary packing facility.
(provide (all-defined-out))

(data Foo (MkFoo Int))

(data Bar (MkBar Foo))

;; A "pass" to run.  You can run this directly with the following command:
;;   gibbon --bench pass --bench-input "foo.bin" 
(define (pass [x : Bar]) : Bar
  (case x
    [(MkBar foo)
     (MkBar 
      (case foo
        [(MkFoo i) (MkFoo (+ i 1))]))]))


;; Here's what it would look like to run the tests from within the
;; gibbon code itself.

;; (define (main) : Bar
;;   (let ([x : Bar (ann (read-packed "test24_input.bin") Bar)])
;;     (iterate (pass x))))

;; But for this we need string literals!
