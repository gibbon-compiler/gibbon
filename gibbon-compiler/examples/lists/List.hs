module List where

cmp1 :: (Int, Int) -> (Int, Int) -> Int
cmp1 a b = (a !!! 0) - (b !!! 0)

sort :: [(Int, Int)] -> [(Int, Int)]
sort ls =
  let ls2 = vsort ls cmp1
  in ls2

gibbon_main =
    let ls :: [(Int,Int)]
        ls  = vempty
        ls2 = vsnoc ls (40,50)
        ls3 = vsnoc ls2 (10,20)
        ls4 = vsort ls3 cmp1
        x   = vnth 0 ls3
        y   = vnth 0 ls4
    in (x !!! 0, x !!! 1, y !!! 0, y !!! 1)
