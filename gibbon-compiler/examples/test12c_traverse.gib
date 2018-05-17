#lang gibbon

;; Data type of unknown size.
(data Nat [Zero] [Suc Nat])

;; A field stored after the unknown-sized packed object.
(data Foo [MkFoo Nat Int])

(define (trav [x : Nat]) : Int
  (case x
    [(Zero) 0]
    [(Suc n) (+ 1 (trav n))]))

;; Access something after a dynamically-sized field:
(case (MkFoo (Suc (Zero)) 71)
  ;; This needs no copy insertion.  Just witnessing.
  [(MkFoo q s)
   (let ([ignored : Int (trav q)])
     s)])
