#lang gibbon

(data Foo (MkFoo (Listof Int)))

(define (add1 [x : Foo]) : Foo
  (case x
    [(MkFoo ls)
     (MkFoo (for/list ([ x : Int ls]) (+ 1 x)))]))


(add1 (MkFoo (list 1 2 3)))

;; (let ((y : Foo (add1 (MkFoo (list 1 2 3)))))
;;   42)
