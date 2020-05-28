module InPlaceList where

cmp1 :: (Int, Int) -> (Int, Int) -> Int
cmp1 a b = (a !!! 0) - (b !!! 0)

sort :: Vector (Int,Int) -> Vector (Int,Int)
sort ls =
  let ls2 = vsort ls cmp1
  in ls2

gibbon_main =
    let ls :: Vector (Int,Int)
        ls  = vempty
        _   = inplacevsnoc ls (40,50)
        tup = vnth 0 ls
        _   = inplacevsnoc ls (10,20)
        _   = inplacevsort ls cmp1
        tup2 = vnth 0 ls
    in (tup !!! 0, tup !!! 1, tup2 !!! 0, tup2 !!! 1)
