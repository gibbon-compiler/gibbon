#lang gibbon

(let ([d : (SymDict Int) (ann (empty-dict) (SymDict Int))])
  (let ([d2 : (SymDict Int) (insert d (quote x) (ann 2 Int))])
    (let ([d3 : (SymDict Int) (insert d2 (quote y) (ann 5 Int))])
      (let ([d4 : (SymDict Int) (insert d2 (quote y) (ann 10 Int))])
        (+ (ann (lookup d4 (quote y)) Int)
           (ann (lookup d3 (quote y)) Int))))))
