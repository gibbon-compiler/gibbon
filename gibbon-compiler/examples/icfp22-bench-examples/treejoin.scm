#!chezscheme
(import (chezscheme))

;; tree
(define-record-type node (fields key tree-left tree-right))
(define-record-type leaf (fields key element))
(define-record-type empty)
(define-record-type error-node)

;; maybe
(define-record-type just (fields element))
(define-record-type nothing)

(define (insert-t k e t)
  (cond ((node? t)
         (let ([k1 (node-key t)]
               [l (node-tree-left t)]
               [r (node-tree-right t)])
           (if (<= k k1)
               (make-node k1 (insert-t k e l) r)
               (make-node k1 l (insert-t k e r)))))
        ((leaf? t)
         (let ([k1 (leaf-key t)]
               [v (leaf-element t)])
           (if (< k k1)
               (make-node k (make-leaf k e) (make-leaf k1 v))
               (if (> k k1)
                   (make-node k1 (make-leaf k1 v) (make-leaf k1 e))
                   (make-error-node)))))
        ((empty? t) (make-leaf k e))
        ((error-node? t) t)))

(define (lookup-t k t)
  (cond ((node? t)
         (let ([k1 (node-key t)]
               [l (node-tree-left t)]
               [r (node-tree-right t)])
           (if (<= k k1)
               (lookup-t k l)
               (lookup-t k r))))
        ((leaf? t)
         (let ([k1 (leaf-key t)]
               [v (leaf-element t)])
           (if (= k k1) (make-just v) (make-nothing))))
        ((empty? t) (make-nothing))
        ((error-node? t) (make-nothing))))

(define (mktree fk pts t)
  (if (null? pts) t
      (mktree fk (cdr pts) (insert-t (fk (car pts)) (car pts) t))))

(define (join t1 t2 j)
  (cond ((node? t1)
         (let ([k (node-key t1)]
               [l (node-tree-left t1)]
               [r (node-tree-right t1)])
           (cond ([node? t2]
                  (join l t2 (join r t2 j)))
                 ([leaf? t2]
                  (join l t2 (join r t2 j)))
                 ([empty? t2] j)
                 ([error-node? t2] t2))))
        ((leaf? t1)
         (let ([k1 (leaf-key t1)]
               [v (leaf-element t1)])
           (let ([a (fxvector-ref v 0)]
                 [b (fxvector-ref v 1)]
                 [c (fxvector-ref v 2)])
             (let* ([t2 (lookup-t c t2)]
                    [res (cond ((nothing? t2) j)
                               ((just? t2)
                                (let ([w (just-element t2)]
                                      [d (fxvector-ref (just-element t2) 0)]
                                      [e (fxvector-ref (just-element t2) 1)])
                                  (insert-t c (fxvector a b c d e) j))))])
               (cond ((node? t2) res)
                     ((leaf? t2) res)
                     ((empty? t2) j)
                     ((error-node? t2) t2))))))
        ((empty? t1) j)
        ((error-node? t1) t1)))

;; awkward string manipulation
(define (string-split str delim)
  (define in (open-input-string str))
  (let loop ((rv '()) (out (open-output-string)))
    (define c (read-char in))
    (cond ((eof-object? c)
           (reverse (cons (get-output-string out) rv)))
          ((char=? c delim)
           (loop (cons (get-output-string out) rv)
                 (open-output-string)))
          (else
           (write-char c out)
           (loop rv out)))))

;; read list of vectors from file
(define (read-array-file f)
  (call-with-input-file f
    (lambda (p)
      (let loop ((acc '()))
        (let ([line (get-line p)])
          (if (eof-object? line) (reverse acc) ;; reverse to maintain correct order of vectors
              (let* ([strs (string-split line #\space)]
                     [vec (list->fxvector (map string->number strs))])
                (loop (cons vec acc)))))))))

(let* ([f (read-array-file "treejoin.txt")]
       ;; double-check this! assumes input list has even length
       [len (length f)]
       [half (/ len 2)]
       [f1 (list-head f half)]
       [f2 (list-tail f half)]
       [fk (lambda (x) (fxvector-ref x 0))]
       [t1 (mktree fk f1 (make-empty))]
       [t2 (mktree fk f2 (make-empty))]
       [res (join t1 t2 (make-empty))])
  res)
