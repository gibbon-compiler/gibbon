module List where

head1 :: [(Int,Int)] -> (Int, Int)
head1 ls =
    let x = vnth 0 ls
    in x

gibbon_main =
    let ls :: [(Int,Int)]
        ls  = vempty
        ls2 = vsnoc ls (10,20)
        x   = vnth 0 ls2
        ls3 = vsnoc ls2 (40,50)
        y   = vnth 0 ls3
    in (x !!! 0, x !!! 1, y !!! 0, y !!! 1)
