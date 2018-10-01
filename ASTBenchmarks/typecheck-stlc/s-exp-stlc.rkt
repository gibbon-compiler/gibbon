#lang racket

(provide typecheck-expr
         type?)
(require (rename-in racket/unsafe/ops
                    [unsafe-car ucar]
                    [unsafe-cdr ucdr]))

#| http://www.cs.cornell.edu/courses/cs6110/2013sp/lectures/lec25-sp13.pdf

   Simply-typed lambda calculus

   prim values b ::= n | true | false | null
   terms       e ::= b | x | e1 e2 | lambda x:t . e
   prim types  B ::= int | bool | 1
   types       t ::= t1 -> t2 | B

|#

(define empty-env '())

(define (extend-env env sym val)
  (cons (cons sym val) env))

(define (apply-env env sym)
  (cond
    [(empty? env)
     (error 'apply-env "Could not find variable" sym)]
    [(eq? (ucar (ucar env)) sym)
     (ucdr (ucar env))]
    [else
     (apply-env (ucdr env) sym)]))
     

(define (type? t)
  (match t
    [(or 'int 'bool 'ntype)
     #t]
    [ls  ;; `(,t1 -> ,t2)   turn to `(result params)
     (if (or (not (list? ls)) (empty? (cdr ls)))
         #f
         (and (andmap type? (ucdr ls)) (type? (ucar ls))))]
    [_
     #f]))

(define (type-equal? t1 t2)
  (match* (t1 t2)
    [('int 'int)
     #t]
    [('bool 'bool)
     #t]
    [('ntype 'ntype)
     #t]
    [(ls1 ls2)    ;;(`(,t1_ -> ,t2_) `(,t1__ -> ,t2__))
     (if (or (not (and (list? ls1) (list? ls2)))
              (empty? (cdr ls1))
              (empty? (cdr ls2)))
         #f
         (and (andmap type-equal? (ucdr ls1) (ucdr ls2))
              (type-equal? (ucar ls1) (ucar ls2))))]
    [(_ _)
     #f]))

;; from  2,764,194,400 bytes allocated in the heap
;; to  1,680,458,704 bytes allocated in the heap
;; to 910,630,272 bytes allocated in the heap

(define (typecheck expr tenv) ;; replace tenv with alist
  (match expr
    [(? exact-integer? n)
     'int]
    [(or 'true 'false)
     'bool]
    ['null
     'ntype]
    [(? symbol? x)
     (apply-env tenv x)]
    [`(begin ,expr)
     (for/last ([e (in-vector expr)])
       (typecheck e tenv))]
    [`(lambda ,args ,body)
     (let ([new-tenv (for/fold ([tenv_ tenv])
                               ([arg (in-vector args)])
                       (extend-env tenv_ (ucar arg) (ucar (ucdr (ucdr arg)))))])
       (cons (typecheck body new-tenv)
             (for/list ([a (in-vector args)])
               (ucar (ucdr (ucdr a))))))]
    [`(,e1 . ,e2)
     (match (typecheck e1 tenv)
       [ls;;`(,t1 -> ,t2) ;; represent types differently.
        (if (or (not (list? ls)) (empty? (cdr ls)))
            (error 'typecheck "no type ~a~n" expr)
            (if (andmap (lambda (t_ e_)
                          (type-equal? t_ (typecheck e_ tenv)))
                        (ucdr ls) e2)
                (ucar ls)
                (error 'typecheck "no type: ~a~n" expr)))]
       [else
        (error 'typecheck "no type ~a~n" expr)])]
    [else  ;; i think the previous expression will capture some of the "else" as well
     (error 'typecheck "bad form: ~a" expr)]))

(define (typecheck-expr expr)
  (typecheck expr empty-env))