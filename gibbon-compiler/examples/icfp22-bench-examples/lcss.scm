#!chezscheme
(import (chezscheme))

(define (snd-list tuple-list)
  (map (lambda (x) (fxvector-ref x 1)) tuple-list))

(define (algb2 x k0j1 k1j1 mlist)
  (if (null? mlist) '()
      (let* ([y (fxvector-ref (car mlist) 0)]
             [k0j (fxvector-ref (car mlist) 1)]
             [kjcurr (if (= x y) (+ k0j 1) (fxmax k1j1 k0j))]
             [newtup (fxvector y kjcurr)])
        (cons newtup (algb2 x k0j kjcurr (cdr mlist))))))

(define (algb1 list1 ys)
  (if (null? list1) (snd-list ys)
      (algb1 (cdr list1) (algb2 (car list1) 0 0 ys))))

(define (zero-tuple-list list)
  (map (lambda (x) (fxvector x 0)) list))

(define (algb xs ys)
  (cons 0 (algb1 xs (zero-tuple-list ys))))

(define (zip l1 l2)
  (if (null? l1) '()
      (if (null? l2) '()
          (cons (fxvector (car l1) (car l2)) (zip (cdr l1) (cdr l2))))))

(define (take num ls)
  (if (null? ls) '()
      (if (> num 0)
          (cons (car ls) (take (- num 1) (cdr ls)))
          '())))

(define (drop num ls)
  (if (null? ls) '()
      (if (<= num 0) ls (drop (- num 1) (cdr ls)))))

(define (findk k km m ls)
  (if (null? ls) km
      (let ([x (fxvector-ref (car ls) 0)]
            [y (fxvector-ref (car ls) 1)])
        (if (>= (+ x y) m)
            (findk (+ k 1) k (+ x y) (cdr ls))
            (findk (+ k 1) km m (cdr ls))))))

(define (algc m n xs ys ys1)
  (if (null? ys) ys1
      (if (null? xs) '()
          (if (null? (cdr xs))
              (if (member (car xs) ys)
                  (cons (car xs) ys1)
                  ys1)
              (let* ([xs1 (take (/ m 2) xs)]
                     [xs2 (drop (/ m 2) xs)]
                     [l1 (algb xs1 ys)]
                     [l2 (reverse (algb (reverse xs2) (reverse ys)))]
                     [k (findk 0 0 -1 (zip l1 l2))]
                     [algc1 (algc (- m (/ m 2)) (- n k) xs2 (drop k ys) ys1)]
                     [algc2 (algc (/ m 2) k xs1 (take k ys) algc1)])
                algc2)))))

(define (lcss xs ys)
  (algc (length xs) (length ys) xs ys '()))

(define (make-int-list start end skip-factor)
  (if (<= start end)
      (cons start (make-int-list (+ start skip-factor) end skip-factor))
      '()))

(define (read-array-file f)
  (call-with-input-file f
    (lambda (p)
      (let loop ((acc '()))
        (let ([line (get-line p)])
          (if (eof-object? line) (reverse acc)
              (loop (cons (string->number line) acc))))))))

(let* ([f (read-array-file (cadr (command-line)))]
       [a1 (list-ref f 0)]
       [b1 (list-ref f 1)]
       [c1 (list-ref f 2)]
       [d1 (list-ref f 3)]
       [e1 (list-ref f 4)]
       [f1 (list-ref f 5)]
       [l1 (make-int-list a1 c1 (- b1 a1))]
       [l2 (make-int-list d1 f1 (- e1 d1))]
       [l3 (lcss l1 l2)]
       ;[l5 (make-int-list (list-ref f 6) (list-ref f (- (length f) 1)) (- (list-ref f 7) (list-ref f 6)))]
       ;[t1 (equal? l3 l5)]
       )
  ;(display t1)
  '())
