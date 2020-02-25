module ParFib where

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

fib :: Int -> Int
fib n =
    if n == 0
    then 0
    else if n == 1
    then 1
    else if n < 19
    then fib_seq n
    else
        let x = spawn (fib (n - 1))
            y = fib (n - 2)
            _ = sync
        in x + y

gibbon_main =
    let n = sizeParam
    in iterate (fib n)
