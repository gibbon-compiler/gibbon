module Vector where

-- cmp1 :: (Int, Int) -> (Int, Int) -> Int
-- cmp1 a b = (a !!! 0) - (b !!! 0)

-- sort :: Vector (Int,Int) -> Vector (Int,Int)
-- sort ls =
--   let ls2 = vsort ls cmp1
--   in ls2

fib_seq :: Int -> Int
fib_seq n =
    if n <= 0
    then 0
    else if n == 1
    then 1
    else
        let x = fib_seq (n - 1)
            y = fib_seq (n - 2)
        in x + y

gibbon_main =
    let lam = (\i -> if i > 10 then fib_seq 10 else fib_seq i)
        vec = iterate (vgenerate_par 500 50 lam)
        vec2 = iterate (vgenerate 50 lam)
    in vnth vec 20
