#lang racket

(require "twitter_types.gib")

(define datum (file->value "twitter_input.dat"))

(define (parse-Hashtags hts)
  (match hts
    [`(NilHT) (NilHT)]
    [`(ConsHT ,x ,xs) (ConsHT x (parse-Hashtags xs))]))

(define (parse-Tweet t)
  (match t
    [`(TweetMD ,i ,hts) (TweetMD i (parse-Hashtags hts))]))

(define (parse-Tweets ts)
  (match ts
    [`(NilTW) (NilTW)]
    [`(ConsTW ,x ,xs) (ConsTW (parse-Tweet x) (parse-Tweets xs))]))

(define parsed (parse-Tweets datum))

;; (printf "Input: ~a\n" parsed)

(define bytes (pack-Tweets parsed))

;; (printf "Output: ~s\n" bytes)

(call-with-output-file "twitter_input.gpkd"
  (lambda (outp)
    (printf "Bytes written: ~a\n" (write-bytes bytes outp)))
  #:exists 'replace)

(display "Wrote binary output to file.\n")
