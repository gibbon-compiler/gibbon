module List where

head1 :: [(Int,Int)] -> (Int, Int)
head1 ls =
    let x = vnth 0 ls
    in x

gibbon_main =
    let ls :: [(Int,Int)]
        ls  = vempty
        ls2 = vsnoc ls (10,20)
        n   = vlength ls2
        x   = vnth (n-1) ls2
    in (x !!! 1)
