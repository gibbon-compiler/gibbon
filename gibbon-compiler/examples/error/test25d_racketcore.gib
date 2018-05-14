#lang gibbon

(require "../../ASTBenchmarks/grammar_racket.gib")

;; Non-exhaustive pattern match
(define (foo [e : Toplvl]) : Int
  (case e
    [(Expression x)
      (case x
        [(VARREF s) 1]
        [(Top s) 2]
        [(VariableReference s) 3] 
        [(VariableReferenceTop s) 4]
        [(VariableReferenceNull) 5]
    	[(Quote d) 6]
	[(QuoteSyntax d) 7]
	[(QuoteSyntaxLocal d) 8]
	[(Lambda formals lse) 9]
        [(CaseLambda cases) 10]
        [(LetValues binds body) 11]
        [(LetrecValues binds body) 12]
        [(If cond then else) 13]
        [(Begin exprs) 14]
        [(Begin0 e1 exprs) 15]
        [(App rator rands) 16]
        [(SetBang s e) 17]
        [(WithContinuationMark e1 e2 e3) 18])]))
;; TODO: Need to fill these out with error cases.

(foo (Expression (VARREF (quote hi))))
