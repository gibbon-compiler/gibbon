#!chezscheme
(import (chezscheme))

;; tree
(define-record-type node (fields element left-tree right-tree))
(define-record-type leaf (fields element))
(define-record-type empty)

(define (helper s e)
  (if (< e s) (make-empty)
      (if (= s e) (make-leaf s)
          (let ([m (+ (/ (- e s) 2) s)])
            (make-node m (helper s (- m 1)) (helper (+ m 1) e))))))

(define (sum-tree tr)
  (cond ((empty? tr) 0)
        ((leaf? tr) (leaf-element tr))
        ((node? tr)
         (let ([n (node-element tr)]
               [l (node-left-tree tr)]
               [r (node-right-tree tr)])
           (+ n (+ (sum-tree l) (sum-tree r)))))))

(define (tree-insert tr n)
  (cond ((empty? tr) (make-leaf n))
        ((leaf? tr)
         (let ([n1 (leaf-element tr)])
           (if (< n n1)
               (make-node n1 (make-leaf n) (make-empty))
               (make-node n1 (make-empty) (make-leaf n)))))
        ((node? tr)
         (let ([n1 (node-element tr)]
               [l (node-left-tree tr)]
               [r (node-right-tree tr)])
           (if (< n1 n)
               (make-node n1 l (tree-insert r n))
               (make-node n1 (tree-insert l n) r))))))
