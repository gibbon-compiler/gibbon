#lang racket

(require "lc.gib")

(define (int->intj i)
  (if (zero? i) (ZeroJ) (SuccJ (int->intj (- i 1)))))

(define (gen-var)
  (let ([n (random 15)])
    (int->intj n)))

#;
(define (binds->vars binds)
  (match binds
    [`(NilBinds) (list)]
    [`(ConsBinds ,v ,x ,rst) (cons v (binds->vars rst))]))

(define (gen-lits)
  (let ([n (random 10)])
    (match n
      ;; LitE
      [_ #:when (< n 6)
         (LitE (random 100))]

      ;; PlusE
      [_ (PlusE (gen-lits) (gen-lits))])))

(define (gen-binds max-depth vars depth)
  (let ([n (random 10)])
    (if (and (> n 1) (< n 7))
        (let ([v (gen-var)])
          (let-values ([(vars2 binds) (gen-binds max-depth vars (+ depth 1))])
            (values (append (cons v vars) vars2) (ConsBinds v (gen-expr max-depth vars (+ depth 1)) binds))))
        (values vars (NilBinds)))))

;; vars are variables in scope
(define (gen-expr max-depth vars depth)
  (if (> depth max-depth)
      (if (empty? vars)
          (LitE 10)
          (let [(m (random (length vars)))]
            (VarE (list-ref vars m))))
      (if (< depth (* 0.8 max-depth))
          (let [(n (random 50))]
            (if (< n 25)
                (let ([v (gen-var)])
                  (LetE v (gen-expr max-depth vars (+ depth 1)) (gen-expr max-depth (cons v vars) (+ depth 1))))
                (let-values ([(vars2 binds) (gen-binds max-depth vars depth)])
                  (LetStarE binds (gen-expr max-depth vars (+ depth 1))))))
          (let [(n (random 50))]
            (match n
              ;; VarE
              [0 (if (empty? vars)
                     (LitE 10)
                     (let* [(m (random (length vars)))]
                       (VarE (list-ref vars m))))]
              ;; LitE
              [1 (gen-lits)]

              ;; LetE
              [_ #:when (and (> n 1) (< n 20))
                 (let ([v (gen-var)])
                   (LetE v (gen-expr max-depth vars (+ depth 1)) (gen-expr max-depth (cons v vars) (+ depth 1))))]

              ;; LamE
              [_ #:when (and (>= n 20) (< n 30))
                 (let ([v (gen-var)])
                   (LamE v (gen-expr max-depth (cons v vars) (+ depth 1))))]

              ;; PlusE
              [_ #:when (and (>= n 30) (< n 35))
                 (PlusE (gen-lits) (gen-lits))]

              ;; IncrE
              [_ #:when (and (>= n 35) (< 40))
                 (IncrE (gen-lits))]

              ;; LetStarE
              [_ #:when (and (>= n 40))
                 (let-values ([(vars2 binds) (gen-binds max-depth vars depth)])
                   (LetStarE binds (gen-expr max-depth vars (+ depth 1))))])))))

(module+ main
  (require racket/cmdline)
  (command-line #:args (n-str out out-packed)
                (let* ([max-depth (string->number n-str)]
                       [lc (gen-expr max-depth '() 0)]
                       [bs (pack-Exp lc)])
                  (pretty-print lc (open-output-file out))
                  (write-bytes bs (open-output-file out-packed)))))

#|
(require "../../../ASTBenchmarks/grammar_racket.gib")
(require "../../../ASTBenchmarks/common/racket/parse.rkt")

(define input1
  "(BeginTop (CONSTOPLVL (BeginTop (CONSTOPLVL (BeginTop (CONSTOPLVL (BeginTop (CONSTOPLVL (BeginTop (NULLTOPLVL)) (CONSTOPLVL (Expression (App (VARREF configure) (CONSEXPR (Quote (INTLIT 5)) (NULLEXPR)))) (NULLTOPLVL)))) (NULLTOPLVL))) (CONSTOPLVL (BeginTop (NULLTOPLVL)) (CONSTOPLVL (BeginTop (NULLTOPLVL)) (NULLTOPLVL))))) (NULLTOPLVL)))")

(define input1-sexp (read (open-input-string input1)))

(define (get-first-sym ls)
  (match ls
    [`(CONSSYM ,s ,_) s]
    [`(NULLSYM) (gensym)]))

(define uniq-storage 0)

;; lame hack
(define (uniq)
  (begin
    (set! uniq-storage (+ uniq-storage 1))
    uniq-storage))

(define (int->intj i)
  (if (zero? i) (ZeroJ) (SuccJ (int->intj (- i 1)))))

(define (uniq-var)
  (int->intj (uniq)))

;; env maps symbols to ints
(define (toplvl->lc-expr env top)
  (match top
    [`(DefineValues ,ls ,e)
     (LetE (ZeroJ) (expr->lc-expr env e) (VarE (ZeroJ)))]
    [`(DefineSyntaxes ,ls ,e)
     (LetE (ZeroJ) (expr->lc-expr env e) (VarE (ZeroJ)))]
    [`(BeginTop ,ls)
     (list-toplvl->lc-expr env ls)]
    [`(Expression ,e)
     (expr->lc-expr env e)]))

(define (list-toplvl->lc-expr env ls)
  (match ls
    [`(NULLTOPLVL)
     (LitE 101)]
    [`(CONSTOPLVL ,t ,rst)
     (let ([v (uniq-var)])
       (LetE v (toplvl->lc-expr env t) (list-toplvl->lc-expr env rst)))]))

(define (ls-expr->lc-expr env ls)
  (match ls
    [`(NULLEXPR) (LitE 102)]
    [`(CONSEXPR ,a ,d) (expr->lc-expr env a)]))

(define (sym->var env s)
  (hash-ref env s (uniq-var)))

(define (formals->sym fs)
  (match fs
    [`(F1 ,ls1) (get-first-sym ls1)]
    [`(F2 _ ,s) s]
    [`(F3 ,s)   s]))

(define (lambda-case->expr env lc)
  (match lc
    [`(CONSLAMBDACASE ,fs ,ls ,lc2)
     (let* ([sym (formals->sym fs)]
            [v (sym->var env sym)]
            [env2 (hash-set env fs v)])
       (LetE v (ls-expr->lc-expr env2 ls) (lambda-case->expr env2 lc2)))]
    [`(NULLLAMBDACASE) (LitE 103)]))

(define (lvbind->lc-expr env bod bnds)
  (match bnds
    [`(CONSLVBIND ,ls ,e1 ,rst)
     (let* ([sym (get-first-sym ls)]
            [v (sym->var env sym)])
       (LetE v (expr->lc-expr env e1) (lvbind->lc-expr env bod rst)))]
    [`(NULLLVBIND) bod]))

(define (expr->lc-expr env e)
  (match e
    [`(VARREF ,s) (VarE (hash-ref env s (ZeroJ)))]
    [`(Lambda ,fs ,ls)
     (let* ([sym (formals->sym fs)]
            [v (sym->var env sym)]
            [env2 (hash-set env fs v)])
       (ls-expr->lc-expr env2 ls))]
    [`(CaseLambda ,lc) (lambda-case->expr env lc)]
    [`(If ,a ,b ,c) (expr->lc-expr env b)]
    [`(Begin ,ls) (ls-expr->lc-expr env ls)]
    [`(Begin0 ,e1 ,ls) (ls-expr->lc-expr env ls)]
    [`(LetValues ,bnds ,bod)
     (let ([bod1 (ls-expr->lc-expr env bod)])
       (lvbind->lc-expr env bod1 bnds))]
    [`(LetrecValues ,bnds ,bod)
     (let ([bod1 (ls-expr->lc-expr env bod)])
       (lvbind->lc-expr env bod1 bnds))]
    [`(SetBang ,sym ,e1) (LitE 104)]
    [`(Quote (INTLIT ,i)) (LitE i)]
    [`(QuoteSyntax (INTLIT ,i)) (LitE i)]
    [`(QuoteSyntaxLocal (INTLIT ,i)) (LitE i)]
    [`(WithContinuationMark ,a ,b ,c) (expr->lc-expr env a)]
    [`(App ,e1 ,e2) (AppE (expr->lc-expr env e1) (ls-expr->lc-expr env e2))]
    [`(VariableReference ,sym) (VarE (hash-ref env sym (uniq-var)))]
    [`(VariableReferenceTop ,sym) (VarE (hash-ref env sym (uniq-var)))]
    [`(VariableReferenceNull) (LitE 105)]))

(module+ main
  (require racket/cmdline)
  (command-line #:args (in out)
                (let ([lc (toplvl->lc-expr (hash) (file->value in))])
                  (println lc (open-output-file out)))))
|#
