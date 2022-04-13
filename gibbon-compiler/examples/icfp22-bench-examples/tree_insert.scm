#!chezscheme
(import (chezscheme))

;; tree
(define-record-type node (fields element left-tree right-tree))
(define-record-type leaf (fields element))
(define-record-type empty)

;; random
(define mt (string->list (symbol->string (machine-type))))
(define (parse-machine-type mt)
  (if (equal? (car mt) #\t) ; t for threaded
      (if (and (equal? (cadr mt) #\a) (equal? (caddr mt) #\6)) ;; a6 for arm64
          (if (equal? (cdddr mt) (string->list "osx")) ;; is it osx?
              (load-shared-object "libc.dylib") ;; osx is weird
              (load-shared-object "libc.so.6")) ;; else linux
          (error 'parse-machine-type "unknown system" mt))
      (error 'parse-machine-type "unknown system" mt)))
(parse-machine-type mt)
(define c-rand (foreign-procedure "rand" () int))
(define c-srand (foreign-procedure "srand" (unsigned) void))

(c-srand 42) ;; RANDOM SEED

(define (helper s e)
  (if (fx< e s) (make-empty)
      (if (fx= s e) (make-leaf s)
          (let ([m (fx+ (fx/ (fx- e s) 2) s)])
            (make-node m (helper s (fx- m 1)) (helper (fx+ m 1) e))))))

(define (sum-tree tr)
  (cond ((empty? tr) 0)
        ((leaf? tr) (leaf-element tr))
        ((node? tr)
         (let ([n (node-element tr)]
               [l (node-left-tree tr)]
               [r (node-right-tree tr)])
           (fx+ n (fx+ (sum-tree l) (sum-tree r)))))))

(define (tree-insert tr n)
  (cond ((empty? tr) (make-leaf n))
        ((leaf? tr)
         (let ([n1 (leaf-element tr)])
           (if (fx< n n1)
               (make-node n1 (make-leaf n) (make-empty))
               (make-node n1 (make-empty) (make-leaf n)))))
        ((node? tr)
         (let ([n1 (node-element tr)]
               [l (node-left-tree tr)]
               [r (node-right-tree tr)])
           (if (fx< n1 n)
               (make-node n1 l (tree-insert r n))
               (make-node n1 (tree-insert l n) r))))))

(define (min-tree tr)
  (cond ((leaf? tr) (leaf-element tr))
        ((node? tr) (if (empty? (node-left-tree tr))
                        (node-element tr)
                        (min-tree (node-left-tree tr))))))

(define (tree-delete tr n)
  (cond ((empty? tr) tr)
        ((leaf? tr)
         (if (fx= (leaf-element tr) n)
             (make-empty)
             tr))
        ((node? tr)
         (let ([n1 (node-element tr)]
               [l (node-left-tree tr)]
               [r (node-right-tree tr)])
           (if (= n1 n)
               (cond ((empty? l) r)
                     ((empty? r) l)
                     (else (let* ([k (min-tree r)]
                                  [r1 (tree-delete r k)])
                             (make-node k l r1))))
               (if (fx< n1 n)
                   (make-node n1 l (tree-delete r n))
                   (make-node n1 (tree-delete l n) r)))))))

(define (loop tr i)
  (if (fx= i 0) tr
      (let* ([n (fxmod (c-rand) 1000)]
             [tr1 (if (fx= (fxmod n 2) 0)
                      (tree-insert tr n)
                      (tree-delete tr (fx- n 1)))])
        (loop tr1 (- i 1)))))

;; (define (loop tr n)
;;   (if (fx= n 0) tr
;;       (let ([j (fxmod (c-rand) 100)])
;;         (loop (tree-insert tr j) (fx- n 1)))))

(let* ([m (string->number (cadr (command-line)))]
       [total-nodes (fx- (expt 2 (fx+ m 1)) 1)]
       [tr0 (helper 0 total-nodes)]
       [tr1 (loop tr0 1000)])
  (display (sum-tree tr1)))
