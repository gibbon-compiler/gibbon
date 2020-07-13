module Fib where

fib_seq :: Int -> Int
fib_seq n =
    if n == 0
    then 0
    else if n == 1
    then 1
    else
        let x = fib_seq (n - 1)
            y = fib_seq (n - 2)
        in x + y

fib_par :: Int -> Int -> Int
fib_par cutoff n =
    if n == 0
    then 0
    else if n == 1
    then 1
    else if n < cutoff
    then fib_seq n
    else
        let x = spawn (fib_par cutoff (n - 1))
            y = fib_par cutoff (n - 2)
            _ = sync
        in x + y
