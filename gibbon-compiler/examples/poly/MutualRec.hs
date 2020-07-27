module MutualRec where

even :: (Int -> Int) -> Int -> Bool
even f n = if (f n) == 0
           then True
           else odd f (n-1)

odd :: (Int -> Int) -> Int -> Bool
odd f n = if (f n) == 1
           then True
           else even f (n-1)

gibbon_main = even (\i -> i) 10
