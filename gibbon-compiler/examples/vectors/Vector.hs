module Vector where

import Gibbon.Vector

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

-- main = do
--     let lam = (\i -> if i > 10 then fib_seq 10 else fib_seq i)
--         ls = [lam i | i <- [0..4]]
--         ls2 = [lam i | i <- [0..49]]
--         i = foldl (\i acc -> i + acc) 0 (ls++ls2)
--     print i
-- -- 2295

gibbon_main =
    let lam = (\i -> if i > 10 then fib_seq 10 else fib_seq i)
        vec = iterate (generate 5 lam)
        vec2 = iterate (generate_par 50 lam)
        vec3 = iterate (append vec vec2)
        vec4 = iterate (append_par vec vec2)
        vec5 = iterate (map (\i -> i+1) vec4)
        vec6 = iterate (map_par (\i -> i+1) vec4)
        vec7 = iterate (update vec4 3 100)
        vec8 = iterate (update_par vec4 3 100)
        i9 = foldl (\acc i -> i + acc) 0 vec4
        i10 = foldl1_par (\acc i -> i + acc) 0 vec4
        i11 = foldl2_par (\acc i -> i + acc) 0 (\a b -> a+b) vec4

        test1 = (nth vec2 4) == 3
        test2 = (nth vec4 54) == 55
        test3 = (nth vec6 54) == 56
        test3 = (nth vec8 54) == 55
        test4 = (i9 == 2295) && (i9 == i10) && (i9 == i11)
    in test1 && test2 && test3 && test4
