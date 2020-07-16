module DataVector where

import Gibbon.Vector

data Ints = MkInts (Vector (Int, Int))

mkInts :: Int -> Ints
mkInts n =
    let vec :: Vector (Int, Int)
        vec = generate n (\i -> (i, i))
    in MkInts vec

sumInts' :: (Vector (Int, Int)) -> Int
sumInts' ls = foldl (\acc (p :: (Int, Int)) ->
                         let (x,y) = p
                         in acc + x + y)
                    0
                    ls

sumInts :: Ints -> Int
sumInts is =
    case is of
        MkInts ls -> sumInts' ls

gibbon_main = sumInts (mkInts 11)
