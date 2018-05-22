#lang gibbon

(data Foo (MkFoo (Listof Int)))

(define (sum [x : Foo]) : Int
  (case x
    [(MkFoo ls)
     (for/fold ([acc : Int 0]) ([ x : Int ls])
       (+ acc x))]))

;; No good way to construct lists within treelang currently [2016.11.03]:
;; (sum (MkFoo '(1 2 3)))
