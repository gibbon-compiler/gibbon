#lang typed/racket/base

(provide Int Sym Bool Float SymDict data empty-dict lookup insert delete
         has-key? case
         define let  if :
         for/list for/fold or and
         Vector vector vector-ref
         list and empty? error
         eq? = Listof True False
         sym-append

         time + * - div mod < > rand exp
         size-param iterate

         fl- fl+ fl* fl/ flsqrt fl> fl< flsqrt


         provide require only-in all-defined-out
         ;; So that we can import the treelang progs without runninga
         module+

         pack-Int pack-Bool pack-Sym pack-Float

         #%app #%module-begin #%datum quote
         ann
         ;; "Open" mode:
         #;(all-from-out typed/racket))

(require (prefix-in r typed/racket/base)
         racket/performance-hint
         racket/unsafe/ops
         typed/racket/unsafe
         racket/flonum
         racket/match
         racket/list
         (for-syntax racket/syntax syntax/parse racket/base))

;; add for/list  w/types

#| Grammar

prog := #lang gibbon
d ... f ... e

;; Data definitions:
d := (data T [K fTy ...] ...)

;; Function definitions
f := (define (f [v : t] ...) : t e)

;; Field types
fTy := t | (Listof t)

;; Types
t := Int | Sym | Bool
| (Vector t ...)
| (SymDict t) ;; maps symbols to t?
| T

e := var | lit
| (f e ...)
| (vector e ...)
| (vector-ref e int)
| (K e ...)
| (case e [(K v ...) e] ...)
| (let ([v : t e] ...) e)        :: CHANGED THIS, note the :
| (if e e e)
| primapp
| (for/list ([v : t e])  e)      ;; not enforced that only loops over single list
| (error string)
| (time e)                       ;; time a benchmark

primapp := (binop e e)
| (insert e e e)
| (lookup e e)
| (empty-dict)

binop := + | - | *

lit := int | #t | #f

;; Example "hello world" program in this grammar:

(data Tree
      [Leaf Int]
      [Node Tree Tree])
'
(define (add1 [x : Tree]) : Tree
  (case x
    [(Leaf n)   (Leaf (+ n 1))]
    [(Node x y) (Node (add1 x) (add1 y))]))

|#

;; CONSIDERING, but not aded yet:
;;        | (dict-size e)


;;(case e [(K v ...) e] ...)
(define-syntax (case stx)
  (syntax-parse stx
    [(case v [(~and pat (S:id p:id ...)) rhs] ...)
     (syntax/loc stx
       (match v
         [pat rhs] ...))]
    [(case v [(~and pat (S:id p:id ...)) rhs] ... [_ rhs*])
     (syntax/loc stx
       (match v
         [pat rhs] ...
         [_ rhs*]))]))


;;(insert e e e)
(define-syntax-rule (insert ht key v)
  (hash-set ht key v))

(define-syntax-rule (lookup ht key)
  (hash-ref ht key))

(define-syntax-rule (empty-dict)
  (hash))

(define-syntax-rule (delete ht key)
  (hash-remove ht key))

(define-syntax-rule (has-key? ht key)
  (hash-has-key? ht key))

(define-syntax-rule (time e)
  (let-values ([(ls cpu real gc) (time-apply (lambda () e) '())])
    ;; RRN: This causes problems, and it only really makes sense if
    ;; time is the "iterate" function as well.
    ; (printf "BATCHTIME: ~a\n" (/ (exact->inexact real) 1000.0))
    (printf "SELFTIMED: ~a\n" (/ (exact->inexact real) 1000.0))
    (match ls
      [(list x) x])))

#;
(define-syntax-rule (iterate e)
  (let ((run (lambda () e)))
    (printf "ITERS: ~a\n" (iters-param))
    (let loop ([res (run)]
               [count (sub1 (iters-param))])
      (if (zero? count)
          res
          (loop (run) (sub1 count))))))

(: run-n (All (a) (-> Integer (-> a) a)))
(define (run-n n f)
  (if (r= 1 n) (f)
      (begin (f)
             (run-n (sub1 n) f))))
(define-syntax-rule (iterate e)
  (begin (printf "ITERS: ~a\n" (iters-param))
         (printf "SIZE: ~a\n" (size-param))
         (let-values ([(ls cpu real gc)
                       (time-apply (lambda () (run-n (iters-param)
                                                     (lambda () e))) '())])
           (printf "BATCHTIME: ~a\n" (/ (exact->inexact real) 1000.0))
           (match ls
             [(list x) x]))))

(: sym-append (-> Symbol Integer Symbol))
(define (sym-append [sym : Symbol] [i : Integer])
  (string->symbol (string-append (symbol->string sym) (number->string i))))


(define-type Int Fixnum)
(define-type Sym Symbol)
(define-type Bool Boolean)
(define-type Float Flonum)
(define-type (SymDict t) (HashTable Symbol t))

(define-values (prop:pack pack? pack-ref) (make-struct-type-property 'pack))

(define (pack-Int [i : Int]) (integer->integer-bytes i 8 #true))
(define (pack-Float [f : Float]) (real->floating-point-bytes f 8))
(define (pack-Bool [b : Bool]) (if b (bytes 1) (bytes 0)))
(define (pack-Sym [s : Sym]) : Bytes
  (let ([i : Int (foldr (lambda (i acc) (* i acc)) 1 (map char->integer (string->list (symbol->string s))))])
    (integer->integer-bytes i 8 #true)))


(define-syntax (data stx)
  (syntax-case stx ()
    [(_ type1 [ts f ...] ...)
     (with-syntax ([((f-ids ...) ...)
                    (map generate-temporaries (syntax->list #'((f ...) ...)))]
                   [(tag-num ...)
                    (build-list (length (syntax->list #'((f ...) ...))) values)]
                   [pack-id (format-id #'type1 "pack-~a" #'type1)]
                   [((pack-f-ids ...) ...)
                    (map (λ (fs) (map (λ (f)
                                        (if (identifier? f)
                                            (format-id f "pack-~a" f)
                                            #'(λ (v) (bytes)))) ;; doesn't work, but we should switch to no-list
                                      (syntax->list fs)))
                         (syntax->list #'((f ...) ...)))])
       #'(begin
           (define-type type1 (U ts ...))

           (struct ts ([f-ids : f] ...) #:transparent) ...
           (define (pack-id [v : type1]) : Bytes
             (match v
               [(ts f-ids ...) (bytes-append (bytes tag-num) (pack-f-ids f-ids) ...)]
               ...))))]))

(define True  : Bool #t)
(define False : Bool #f)

(begin-encourage-inline
  ;; FIXME: need to make sure these inline:
  (define (+ [a : Int] [b : Int]) : Int
    (unsafe-fx+ a b))

  (define (- [a : Int] [b : Int]) : Int
    (unsafe-fx- a b))

  (define (* [a : Int] [b : Int]) : Int
    (unsafe-fx* a b))

  (define (div [a : Int] [b : Int]) : Int
    (unsafe-fxquotient a b))

  (define (eq? [a : Sym] [b : Sym]) : Bool
    (req? a b))

  (define (= [a : Int] [b : Int]) : Bool
    (req? a b))

  (define (mod [a : Int] [b : Int]) : Int
    (unsafe-fxremainder a b))

  (define (exp [base : Int] [pow : Int]) : Int
    (unsafe-fl->fx (flexpt (unsafe-fx->fl base) (unsafe-fx->fl pow))))

  ;; Constrained to the value of RAND_MAX (in C) on my laptop: 2147483647 (2^31 − 1)
  (define (rand) : Int
    (random 2147483647))
  )

(define size-param  : (Parameter Int) (make-parameter 1))
(define iters-param : (Parameter Integer) (make-parameter 1))


#|
(data Tree
      [Leaf Int]
      [Node Tree Tree])

(define (add1 [x : Tree]) : Tree
  (case x
    [(Leaf n)   (Leaf (+ n 1))]
    [(Node x y) (Node (add1 x) (add1 y))]))
|#

(match (current-command-line-arguments)
  [(vector s i) (size-param  (cast (string->number s) Int))
                (iters-param (cast (string->number i) Integer))
                ;(printf "SIZE: ~a\n" (size-param))
                #;(printf "ITERS: ~a\n" (iters-param))]
  [(vector s)   (size-param  (cast (string->number s) Int))
                #;(printf "SIZE: ~a\n" (size-param))]
  [(vector)     (void)]
  [args (error (format "Usage error.\nExpected 0-2 optional command line arguments <size> <iters>, got ~a:\n  ~a"
                       (vector-length args) args))])

(module reader syntax/module-reader
  gibbon)
