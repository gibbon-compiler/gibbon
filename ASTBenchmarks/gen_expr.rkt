#lang racket

(define (gen-lam n tyin tyout)
  `(Lam ,(gen-listparam tyin)
        ,(gen-expr (sub1 n) tyout)))

(define (gen-listparam tys)
  (if (null? tys)
      `(NULLPARAM)
      `(CONSPARAM (P (S ',(gensym)) ,(car tys))
                  ,(gen-listparam (cdr tys)))))

(define (gen-expr n ty)
  (if (< n 1)
      (gen-terminal ty)
      (let ([tyin (random-types (random 0 5))]
            [tyout (car (random-types 1))])
        `(App ,(gen-lam (sub1 n) tyin tyout)
              ,(gen-listexpr (sub1 n) tyin)))))

(define (gen-terminal ty)
  (match ty
    [`(Int_) `(N ,(random 0 10))]
    [`(Bool_) `(B ,(if (> (random) 0.5) 'False 'True))]
    [`(NullT) '(Null)]
    [`(Lamt ,tyin ,tyout) (gen-lam 1 tyin tyout)]))

(define (gen-listexpr n tys)
  (if (null? tys)
      `(NULLEXPR)
      `(CONSEXPR ,(gen-expr (sub1 n) (car tys))
                 ,(gen-listexpr n (cdr tys)))))

(define (random-types n)
  (if (zero? n) '()
      (let* ([r (random 0 3)]
             [ty (case r
                   [(0) '(Int_)]
                   [(1) '(Bool_)]
                   [(2) '(NullT)])])
        (cons ty (random-types (sub1 n))))))