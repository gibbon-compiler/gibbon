module DataList where

data Ints = MkInts [Int]

mkInts' :: Int -> [Int] -> [Int]
mkInts' n acc =
    if n == 0
    then acc
    else let _ = inplacevsnoc acc n
         in mkInts' (n-1) acc

mkInts :: Int -> Ints
mkInts n =
    let acc :: [Int]
        acc = vempty
        _ = mkInts' n acc
    in MkInts acc

sumInts'' :: Int -> Int -> [Int] -> Int -> Int
sumInts'' i n ls acc =
    if i == n
    then acc
    else sumInts'' (i+1) n ls (acc + (vnth i ls))

sumInts' :: [Int] -> Int
sumInts' ls = sumInts'' 0 (vlength ls) ls 0

sumInts :: Ints -> Int
sumInts is =
    case is of
        MkInts ls -> sumInts' ls


gibbon_main = sumInts (mkInts 10)
