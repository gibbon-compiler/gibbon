module DataList where

import Gibbon.Vector

data Ints = MkInts (Vector Int)

mkInts :: Int -> Ints
mkInts n =
    let vec :: Vector Int
        vec = vgenerate n (\i -> i)
    in MkInts vec

sumInts'' :: Int -> Int -> (Vector Int) -> Int -> Int
sumInts'' i n ls acc =
    if i == n
    then acc
    else sumInts'' (i+1) n ls (acc + (vnth ls i))

sumInts' :: (Vector Int) -> Int
sumInts' ls = sumInts'' 0 (vlength ls) ls 0

sumInts :: Ints -> Int
sumInts is =
    case is of
        MkInts ls -> sumInts' ls


gibbon_main = sumInts (mkInts 11)
