module Vector where

import Gibbon.Vector
import Gibbon.Vector.Parallel

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

-- -- main = do
-- --     let lam = (\i -> if i > 10 then fib_seq 10 else fib_seq i)
-- --         ls = [lam i | i <- [0..4]]
-- --         ls2 = [lam i | i <- [0..49]]
-- --         i = foldl (\i acc -> i + acc) 0 (ls++ls2)
-- --     print i
-- -- -- 2295

gibbon_main =
    let lam = (\i -> if i > 10 then fib_seq 10 else fib_seq i)
        vec = (generate 5 lam)
        vec2 = (generate_par 50 lam)
        vec3 = (append vec vec2)
        vec4 = (append_par vec vec2)
        vec5 = (map (\i -> i+1) vec4)
        vec6 = (map_par (\i -> i+1) vec4)
        vec7 = (update vec4 3 100)
        vec8 = (update_par vec4 3 100)
        i9 = foldl (\acc i -> i + acc) 0 vec4
        i10 = foldl1_par (\acc i -> i + acc) 0 vec4
        i11 = foldl2_par (\acc i -> i + acc) 0 (\a b -> a+b) vec4
        vec12 = snoc vec8 8
        vec13 = cons 8 vec8
        vec14 = filter (\x -> (mod x 2) == 0) vec2
        _ = printVec (\i -> printint i) vec14
        _ = printsym (quote "\n")

        test1 = (nth vec2 4) == 3
        test2 = (nth vec4 54) == 55
        test3 = (nth vec6 54) == 56
        test3 = (nth vec8 54) == 55
        test4 = (i9 == 2295) && (i9 == i10) && (i9 == i11)
        test5 = (nth vec12 ((length vec12) - 1)) == 8
        test6 = (nth vec13 0) == 8
    in test1 && test2 && test3 && test4 && test5 && test6
