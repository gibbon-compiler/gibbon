;; MonoTree's three traversals for the tree sweep (gibbon_benchmark.py
;; --tree-sweep), ported from BintreeBench (ECOOP 2017, treebench.ss) and
;; aligned with tree_sweep/programs/*/MonoTree*.hs: every value these depths
;; produce is a fixnum, mkTree d 0 gives every one of the 2^d leaves
;; d(d+1)/2, and every subtree is built separately.
;;
;;   chez --program treebench.so <build|add1|sum> --size-param DEPTH --iterate N
(import (chezscheme))

(define-record-type leaf (fields v))
(define-record-type node (fields l r))

(define (mk-tree d acc)
  (if (fx= d 0)
      (make-leaf acc)
      (make-node (mk-tree (fx- d 1) (fx+ d acc)) (mk-tree (fx- d 1) (fx+ d acc)))))

(define (add1-tree t)
  (if (leaf? t)
      (make-leaf (fx+ (leaf-v t) 1))
      (make-node (add1-tree (node-l t)) (add1-tree (node-r t)))))

(define (sum-tree t)
  (if (leaf? t)
      (leaf-v t)
      (fx+ (sum-tree (node-l t)) (sum-tree (node-r t)))))

(define args (command-line-arguments))
(define (arg flag) (string->number (cadr (member flag args))))

(define (now-s)
  (let ([t (current-time 'time-monotonic)])
    (+ (time-second t) (/ (time-nanosecond t) 1e9))))

(define pass (car args))
(define depth (arg "--size-param"))
(define iters (max 1 (arg "--iterate")))
(define box-in (box #f))

(define (run label thunk)
  (printf "Running pass ~a: \n" label)
  (let loop ([i 0] [times '()] [last #f])
    (if (= i iters)
        (values (reverse times) last)
        (let* ([t0 (now-s)] [r (thunk)] [t1 (now-s)])
          (loop (+ i 1) (cons (- t1 t0) times) r)))))

(define-values (times answer)
  (cond
    [(string=? pass "build")
     (set-box! box-in depth)
     (let-values ([(ts last) (run "buildTree (build)" (lambda () (mk-tree (unbox box-in) 0)))])
       (values ts (sum-tree last)))]
    [(string=? pass "add1")
     (set-box! box-in (mk-tree depth 0))
     (let-values ([(ts last) (run "add1Tree (map)" (lambda () (add1-tree (unbox box-in))))])
       (values ts (sum-tree last)))]
    [(string=? pass "sum")
     (set-box! box-in (mk-tree depth 0))
     (run "sumTree (fold)" (lambda () (sum-tree (unbox box-in))))]
    [else (error 'treebench "pass must be build, add1 or sum")]))

(define (fmt t) (format "~,9f" t))
(printf "ITER TIMES: [")
(let loop ([ts times] [first #t])
  (unless (null? ts)
    (unless first (printf ", "))
    (printf "~a" (fmt (car ts)))
    (loop (cdr ts) #f)))
(printf "]\nEnd\n~a\n" answer)
