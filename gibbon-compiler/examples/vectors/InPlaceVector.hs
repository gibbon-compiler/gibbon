module InPlaceList where

import Gibbon.Vector

cmp1 :: (Int, Int) -> (Int, Int) -> Int
cmp1 a b = (a !!! 0) - (b !!! 0)

sort :: Vector (Int,Int) -> Vector (Int,Int)
sort ls =
  let ls2 = vsort ls cmp1
  in ls2

gibbon_main =
    let ls :: Vector (Int,Int)
        ls  = vgenerate 10 (\i -> (i, 10 - i))
        tup = vnth ls 0
        ls2 = inplacevsort ls cmp1
        tup2 = vnth ls2 0
    in (tup !!! 0, tup !!! 1, tup2 !!! 0, tup2 !!! 1)
