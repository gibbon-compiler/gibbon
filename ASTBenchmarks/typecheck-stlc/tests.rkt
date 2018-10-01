#lang racket

(require "expr-gen-stlc.rkt"
	 "typechecker.gib")


(define expr (gen-well-formed-sexp 2 2))

(typecheck-expr expr)

(define expr2 (gen-well-formed-sexp 5 10))

(typecheck-expr expr2)
