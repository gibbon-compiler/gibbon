#!r6rs
(import (rnrs base)
        (rnrs io ports)
        (rnrs io simple)
        (rnrs programs))

(define (reverse-list ls acc)
  (if (null? ls) acc
      (reverse-list (cdr ls) (cons (car ls) acc))))

(define (create-list n)
  (if (zero? n) '()
      (cons n (create-list (- n 1)))))

(let* ((n (string->number (cadr (command-line))))
       (ls  (create-list n))
       (rls (reverse-list ls '())))
  rls)
