#lang gibbon

(data Nat [Zero] [Suc Nat])

;; This differs only by let-binding the result
;; of the recursion:
(define (count [x : Nat]) : Int
  (case x
    [(Zero) 0]
    [(Suc n)
     (let ([res : Int (count n)])
       (+ 1 res))]))

(count (Suc (Suc (Suc (Zero)))))
