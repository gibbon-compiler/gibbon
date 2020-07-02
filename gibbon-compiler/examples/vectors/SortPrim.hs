module InPlaceList where

import Gibbon.Vector

cmp1 :: (Int, Int) -> (Int, Int) -> Int
cmp1 a b = (a !!! 1) - (b !!! 1)

gibbon_main =
    let ls :: Vector (Int,Int)
        ls  = generate 10 (\i -> (i, 10 - i))
        ls2 = vsort ls cmp1
        i = (vnth ls 0) !!! 0
        j = (vnth ls2 0) !!! 0
        ls3 = inplacevsort ls cmp1
        k = (vnth ls3 0) !!! 0
        test1 = i == 0
        test2 = j == 9
        test3 = k == 9
    in test1 && test2 && test3
