#lang racket

(require "../../../ASTBenchmarks/grammar_racket.gib")
(require "../../../ASTBenchmarks/common/racket/parse.rkt")
(require racket/pretty)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (: enlarge-toplvl-list depth : (ListToplvl -> ListToplvl))
(define (enlarge-toplvl-list depth v)
  (match v
    [(NULLTOPLVL) (NULLTOPLVL)]
    [(CONSTOPLVL t ts)
     (CONSTOPLVL (enlarge-toplvl (add1 depth) t) (enlarge-toplvl-list (add1 depth) ts))]))

;; (: enlarge-toplvl depth : (Toplvl -> Toplvl))
(define (enlarge-toplvl depth v)
  (match v
    [(DefineValues ls-sym e)
     (DefineValues ls-sym (enlarge-expr (add1 depth) e))]
    [(DefineSyntaxes ls-sym e)
     (DefineSyntaxes ls-sym (enlarge-expr (add1 depth) e))]
    [(BeginTop ls)
     (BeginTop (enlarge-toplvl-list (add1 depth) ls))]
    [(Expression e)
     (Expression (enlarge-expr (add1 depth) e))]))

;; (: enlarge-formals depth : (Formals -> Formals))
(define (enlarge-formals depth v)
  (match v
    [(F1 x) (F1 x)]
    [(F2 x y) (F2 x y)]
    [(F3 x) (F3 x)]))

;; (: enlarge-lambdacase depth : (LAMBDACASE -> LAMBDACASE))
(define (enlarge-lambdacase depth v)
  (match v
    [(CONSLAMBDACASE f ls rest)
     (CONSLAMBDACASE f
                     (enlarge-expr-list (add1 depth) ls)
                     (enlarge-lambdacase (add1 depth) rest))]
    [(NULLLAMBDACASE) (NULLLAMBDACASE)]))

;; (: enlarge-listsym depth : ListSym -> ListSym)
(define (enlarge-listsym depth v)
  (match v
    [(CONSSYM s rest) (CONSSYM s rest)]
    [(NULLSYM) (NULLSYM)]))

;; (: enlarge-lvbind depth : (Any -> LVBIND))
(define (enlarge-lvbind depth v)
  (match v
    [(CONSLVBIND x e rest)
     (CONSLVBIND x (enlarge-expr (add1 depth) e) (enlarge-lvbind (add1 depth) rest))]
    [(NULLLVBIND) (NULLLVBIND)]))

;; (: enlarge-datum depth : (Datum -> Datum))
(define (enlarge-datum depth v)
  (match v
    [(INTLIT i) (INTLIT i)]))

;; (: enlarge-expr-list depth : ListExpr -> ListExpr)
(define (enlarge-expr-list depth e)
  (match e
    [(NULLEXPR) (NULLEXPR)]
    [(CONSEXPR e rest)
     (CONSEXPR (enlarge-expr (add1 depth) e) (enlarge-expr-list (add1 depth) rest))]))

;; (: enlarge-expr depth : (Expr -> Expr))
(define (enlarge-expr depth v)
  (match v
    [(VARREF x) (VARREF x)]
    [(Lambda fs rest)
     (Lambda fs (enlarge-expr-list (add1 depth) rest))]
    [(CaseLambda rest)
     (CaseLambda (enlarge-lambdacase (add1 depth) rest))]
    [(If cond then else)
     (let ([ex (If (enlarge-expr (add1 depth) cond) (enlarge-expr (add1 depth) then) (enlarge-expr (add1 depth) else))])
       (if (< depth 10)
           ex
           (If (Quote (INTLIT 0)) ex ex)))]
    [(Begin e) (Begin (enlarge-expr-list (add1 depth) e))]
    [(Begin0 e1 ls)
     (Begin0 (enlarge-expr (add1 depth) e1) (enlarge-expr-list (add1 depth) ls))]
    [(LetValues ls e)
     (LetValues (enlarge-lvbind (add1 depth) ls) (enlarge-expr-list (add1 depth) e))]
    [(LetrecValues ls e)
     (LetrecValues (enlarge-lvbind (add1 depth) ls) (enlarge-expr-list (add1 depth) e))]
    [(SetBang x e)
     (SetBang x (enlarge-expr (add1 depth) e))]
    [(Quote d) (Quote (enlarge-datum (add1 depth) d))]
    [(QuoteSyntax d) (QuoteSyntax (enlarge-datum (add1 depth) d))]
    [(QuoteSyntaxLocal d) (QuoteSyntaxLocal (enlarge-datum (add1 depth) d))]
    [(WithContinuationMark e1 e2 e3)
     (let ([ex (WithContinuationMark
                (enlarge-expr (add1 depth) e1)
                (enlarge-expr (add1 depth) e2)
                (enlarge-expr (add1 depth) e3))])
       (if (< depth 10)
           ex
           (If (Quote (INTLIT 0)) ex ex)))]
    [(App e0 es)
     (let ([ex (App (enlarge-expr (add1 depth) e0)
                    (enlarge-expr-list (add1 depth) es))])
       (if (< depth 10)
           ex
           (If (Quote (INTLIT 0)) ex ex)))]
    [(Top x) (Top x)]
    [(VariableReference x) (VariableReference x)]
    [(VariableReferenceTop x) (VariableReferenceTop x)]
    [(VariableReferenceNull) (VariableReferenceNull)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ main
  (require racket/cmdline)
  (command-line #:args (in out)
                (let* ([tl (parse (file->value in))]
                       ;; [ser (pack-Toplvl tl)]
                       [big (enlarge-toplvl 0 tl)]
                       [_ (displayln "done enlarging")]
                       [bigser (pack-Toplvl big)]
                       [_ (displayln "done packing")]
                       )
                  ;; (displayln (bytes-length ser))
                  (displayln (bytes-length bigser))
                  (write-bytes bigser (open-output-file out))
                  ;; (write-to-file (prett1big) out)
                  ;; (print big (open-output-file out))
                  )))
