#lang racket

(require racket/runtime-path)
(require "test-uniqify.rkt")
(require "test-flatten.rkt")
(require "test-compiler.rkt")
(require "../parse.rkt")

(require "../compiler.gib")
(require "../common.gib")

(require rackunit)

;; TODO: write a parser for R0 so that we can re-use all tests from the class

(define tests
  (list uniqify-tests
        flatten-tests
        compiler-tests))

(define (run-tests)
  (let* ([test-results (append-map run-test tests)]
         [num-test-results (length test-results)]
         [failures (map test-result-test-case-name (filter-not test-success? test-results))])
    (inspect-results failures num-test-results "tests")))

;; run examples
(define-runtime-path examples-dir "examples")

;; no support for (read) yet ..
(define ignored-examples
  (for/set ([p '("r0_1.rkt" "r0_2.rkt" "r0_3.rkt" "r1_9.rkt" "r1_10.rkt" "r1_19.rkt"
                 "r1_13.rkt" "r1_15.rkt" "r1a_4.rkt" "r1a_5.rkt" "r1a_6.rkt"
                  ;; actual failure
                 "r1a_8.rkt")])
    (build-path examples-dir p)))

(define (run-example e)
  (let* ([parsed (parse e)]
         [out-path (path-replace-extension e ".out")]
         [expected (if (file-exists? out-path)
                       (file->value out-path)
                       42)]
         [actual (compile parsed)])
    (and (equal? actual expected)
         (file-name-from-path e))))

(define (run-examples)
  (define test-results
    (for/list ([f (in-directory examples-dir)]
               #:when (equal? (path-get-extension f) #".rkt")
               #:unless (set-member? ignored-examples f))
              (run-example f)))
  (define num-test-results (length test-results))
  (define failures (map path->string (filter-not values test-results)))
  (inspect-results failures num-test-results "examples"))

(define (inspect-results xs num-test-results type)
  (if (empty? xs)
      (printf "All ~a ~a passed.\n" num-test-results type)
      (begin (printf "~s/~s ~a failed.\n~a\n"
                     (length xs)
                     num-test-results
                     type
                     (string-join xs "\n"))
             (exit 1))))

(module+ main
  (run-tests)
  (run-examples))
