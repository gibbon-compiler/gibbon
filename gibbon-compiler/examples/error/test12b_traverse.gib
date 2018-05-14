#lang gibbon

;; Data type of unknown size.
(data Nat [Zero] [Suc Nat])

;; A field stored after the unknown-sized packed object.
(data Foo [MkFoo Nat Int])

(define (trav [x : Nat]) : Int
  (case x
    [(Zero) 0]
    [(Suc n) (+ 1 (trav n))]))

;; Access the first field, which gets an easy witness:
(case (MkFoo (Suc (Zero)) 71) 
  [(MkFoo x y) (trav x)])
