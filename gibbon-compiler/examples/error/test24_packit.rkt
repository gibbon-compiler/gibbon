#lang racket

(require "test24_defs.gib")

(define datum (file->value "test24_input.dat"))

;; These could easily be generated in the future:
(define (parse-Foo s)
  (match s
    [`(MkFoo ,i) (MkFoo i)]))

(define (parse-Bar s)
  (match s
    [`(MkBar ,foo) (MkBar (parse-Foo foo))]))

(define parsed (parse-Bar datum))

(printf "Input: ~a\n" parsed)

(define bytes (pack-Bar parsed))

(printf "Output: ~s\n" bytes)

(call-with-output-file "test24_input.gpkd"
  (lambda (outp)
    (printf "Bytes written: ~a\n" (write-bytes bytes outp)))
  #:exists 'replace)

(display "Wrote binary output to file.\n")

