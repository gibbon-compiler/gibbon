#lang racket

(require "s-exp-stlc.rkt"
	 (except-in "typechecker.gib" typecheck-expr)
         racket/random)

(provide gen-well-formed-sexp)

#| http://www.cs.cornell.edu/courses/cs6110/2013sp/lectures/lec25-sp13.pdf

   Simply-typed lambda calculus

   prim values b ::= n | true | false | null
   terms       e ::= b | x | e1 e2 | lambda x:t . e
   prim types  B ::= int | bool | 1
   types       t ::= t1 -> t2 | B

|#

(define (gen-type)
  (let ([rand (random 3)])
    (cond
      [(= rand 0)
       'int]
      [(= rand 1)
       'bool]
      [else
       (cons (gen-type) (list (gen-type)))])))
     ;;  `(,(list (gen-type)) -> ,(gen-type))])))

(define (gen-prim-value)
  (let ([rand (random 3)])
    (cond
      [(= rand 0) ;; return number
       (random 100)]
      [(= rand 1) ;; return true
       'true]
      [else       ;; return false
       'false])))

(define (gen-begin size ls)
  `(begin ,(for/vector ([_ (in-range size)])
             (gen-prim-value))))

(define (gen-term depth arg-num ls)
  (cond
    [(<= depth 1)
     (let ([rand (random 2)])
       (if (= rand 0)
           (list-ref ls (random (length ls)))
           (gen-prim-value)))]
    [else
     (let ([rand (random 2)])
       (cond
         [(= rand 0) ;; app
          (gen-application (- depth 1) ls)]
         [else ;; lambda
          (gen-lambda depth arg-num ls)]))]))


;; generates nested lambdas.
(define (gen-lambda depth arg-num ls)
  (let ([args (for/list ([_ (in-range arg-num)])
                (gensym))]
        [types (for/list ([_ (in-range arg-num)])
                 (gen-type))])
    `(lambda ,(for/vector ([a (in-list args)]
                           [t (in-list types)])
                `(,a : ,t))
       ,(if (<= depth 1)
            (gen-begin 20 ls) ;; 20 is random
            (gen-lambda (sub1 depth) arg-num (cons args ls))))))
  
;; takes a lambda, generates necessary parameters
(define (gen-parameters lam)
  (match lam
    [`(lambda ,args ,body)
     (define t1 (for/list ([a (in-vector args)])
                  (caddr a)))
     (if (is-lambda? body)
         (cons (map gen-term-w-type t1)
               (gen-parameters body))
         (cons (map gen-term-w-type t1)
               '()))]
    [else
     (error 'gen-application "not a lambda ~v~n" lam)]))

;; constructs an application from lambda and params
(define (gen-application expr params)
  (cond
    [(empty? params)
     expr]
    [else
     (gen-application `(,expr ,@(car params))
                      (cdr params))]))
  
;; expr has type lambda?
(define (is-lambda? expr)
  (match (typecheck-expr expr)
    [ls ;;`(,t1 -> ,t2)
     (list? ls)]
    [_
     #f]))
    
;; generates term with type t
(define (gen-term-w-type t)
  (match t
    ['int
     (random 100)]
    ['bool
     (random-ref (list 'true 'false))]
    ['ntype
     'null]
    [ls   ;;`(,t1 -> ,(? type? t2))
     (if (not (list? ls))
         (error 'gen-term-w-type "not a valid type ~v" t)
         `(lambda ,(for/vector ([t_ (in-list (cdr ls))])
                     (if (type? t_)
                         `(,(gensym) : ,t_)
                         (error 'gen-term-w-type "not a valid type ~v" t_)))
            ,(gen-term-w-type (car ls))))]
    [else
     (error 'gen-term-w-type "not a valid type ~v" t)]))


(define (gen-sexp size)
  (define depth 10)
  (define argnum (floor (/ size depth)))
  (gen-term depth argnum '()))

(random-seed 1)

(define (gen-well-formed-sexp depth arg-num)
  (let ([lam (gen-lambda depth arg-num '())])
    (sexp->treelang (gen-application lam (gen-parameters lam)))))

;; Convert sexp version to treelang version

(define (sexp->treelang expr)
  (match expr
    [(? exact-integer? n)
     (N n)]
    ['true
     (B #t)]
    ['false
     (B #f)]
    ['null
     (Null)]
    [(? symbol? x)
     (S x)]
    [`(begin ,expr) ;; expr is vector
     (Begin (vector->listExpr expr 0))]
    [`(lambda ,params ,body)
     (Lam (vector->listParam params 0)
     	  (sexp->treelang body))]
    [`(,e1 . ,e2)
     (App (sexp->treelang e1)
     	  (list->listExpr e2))]
    [else
     (error "No match for ~a\n" expr)]))

(define (sexp->type expr)
  (match expr
    ['int
     (Int_)]
    ['bool
     (Bool_)]
    ['ntype
     (NullT)]
    [ls
     (Lamt (list->listType (cdr ls))
     	   (sexp->type (car ls)))]
    [else
    (error "Not matching type for ~a\n" expr)]))

(define (list->listType types)
  (if (empty? types)
      (NULLTYPE)
      (CONSTYPE (sexp->type (car types))
      		(list->listType (cdr types)))))

(define (list->listExpr exprs)
  (if (empty? exprs)
      (NULLEXPR)
      (CONSEXPR (sexp->treelang (car exprs))
      		(list->listExpr (cdr exprs)))))

(define (vector->listExpr exprs pos)
  (if (>= pos (vector-length exprs))
      (NULLEXPR)
      (CONSEXPR (sexp->treelang (vector-ref exprs pos))
      		(vector->listExpr exprs (+ 1 pos)))))

(define (vector->listParam params pos)
  (if (>= pos (vector-length params))
      (NULLPARAM)
      (let* ([arg (vector-ref params pos)]
      	     [sym (car arg)]
	     [expr (car (cdr (cdr arg)))])
        (CONSPARAM (P (S sym) (sexp->type expr))
      		   (vector->listParam params (+ 1 pos))))))
