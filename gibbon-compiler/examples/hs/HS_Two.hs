module HS_Two where

import Prelude hiding (succ)

data Tree a = Leaf a
            | Node (Tree a) (Tree a)
  deriving Show

mkTree :: Int -> Tree Int
mkTree n = if n == 0
           then Leaf 1
           else Node (mkTree (n-1)) (mkTree (n-1))

foldrTree :: (a -> b -> b) -> b -> Tree a -> b
foldrTree f acc tr =
  case tr of
    Leaf n   -> f n acc
    Node l r -> let acc1 = foldrTree f acc l
                in foldrTree f acc1 r

plus :: Int -> Int -> Int
plus a b = a + b

sumTree :: Tree Int -> Int
sumTree tr = foldrTree plus 0 tr

gibbon_main = sumTree (mkTree 10)


main :: IO ()
main = print gibbon_main
