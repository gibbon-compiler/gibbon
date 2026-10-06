#lang racket/base
;; MonoTree's three traversals for the tree sweep (gibbon_benchmark.py
;; --tree-sweep), ported from BintreeBench (ECOOP 2017, treebench.rkt) and
;; aligned with tree_sweep/programs/*/MonoTree*.hs: every value these depths
;; produce is a fixnum, mkTree d 0 gives every one of the 2^d leaves
;; d(d+1)/2, and every subtree is built separately.
;;
;;   racket treebench_rkt.zo <build|add1|sum> --size-param DEPTH --iterate N
(require racket/list racket/string)

(struct leaf (v))
(struct node (l r))

(define (mk-tree d acc)
  (if (= d 0)
      (leaf acc)
      (node (mk-tree (- d 1) (+ d acc)) (mk-tree (- d 1) (+ d acc)))))

(define (add1-tree t)
  (if (leaf? t)
      (leaf (+ (leaf-v t) 1))
      (node (add1-tree (node-l t)) (add1-tree (node-r t)))))

(define (sum-tree t)
  (if (leaf? t)
      (leaf-v t)
      (+ (sum-tree (node-l t)) (sum-tree (node-r t)))))

(define args (vector->list (current-command-line-arguments)))
(define (arg flag) (string->number (cadr (member flag args))))

;; Monotonic where this Racket has it (8.x and later), wall-clock otherwise.
(define now
  (dynamic-require 'racket/base 'current-inexact-monotonic-milliseconds
                   (lambda () current-inexact-milliseconds)))
(define (timed thunk)
  (define t0 (now))
  (define r (thunk))
  (values (/ (- (now) t0) 1000.0) r))

(define pass (car args))
(define depth (arg "--size-param"))
(define iters (max 1 (arg "--iterate")))
(define box-in (box #f))

(define (run label thunk)
  (printf "Running pass ~a: \n" label)
  (for/fold ([times '()] [last #f] #:result (values (reverse times) last))
            ([i (in-range iters)])
    (define-values (t r) (timed thunk))
    (values (cons t times) r)))

(define-values (times answer)
  (case pass
    [("build")
     (set-box! box-in depth)
     (define-values (ts last) (run "buildTree (build)" (lambda () (mk-tree (unbox box-in) 0))))
     (values ts (sum-tree last))]
    [("add1")
     (set-box! box-in (mk-tree depth 0))
     (define-values (ts last) (run "add1Tree (map)" (lambda () (add1-tree (unbox box-in)))))
     (values ts (sum-tree last))]
    [("sum")
     (set-box! box-in (mk-tree depth 0))
     (run "sumTree (fold)" (lambda () (sum-tree (unbox box-in))))]
    [else (error "pass must be build, add1 or sum")]))

(define (fmt t) (real->decimal-string t 9))
(printf "ITER TIMES: [~a]\n" (string-join (map fmt times) ", "))
(printf "End\n")
(printf "~a\n" answer)
