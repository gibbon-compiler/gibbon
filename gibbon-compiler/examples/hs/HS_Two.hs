module HS_Two where

import Prelude hiding (succ, and)

data Tree a = Leaf a
            | Node (Tree a) (Tree a)
  deriving Show

mkTree :: Int -> a -> Tree a
mkTree d x = if d == 0
             then Leaf x
             else Node (mkTree (d-1) x) (mkTree (d-1) x)

fmapTree :: (a -> b) -> Tree a -> Tree b
fmapTree f tr =
  case tr of
    Leaf x   -> Leaf (f x)
    Node l r -> Node (fmapTree f l) (fmapTree f r)

foldrTree :: (a -> b -> b) -> b -> Tree a -> b
foldrTree f acc tr =
  case tr of
    Leaf n   -> f n acc
    Node l r -> let acc1 = foldrTree f acc l
                in foldrTree f acc1 r

succ :: Int -> Int
succ x = x + 1

plus :: Int -> Int -> Int
plus a b = a + b

and :: Bool -> Bool -> Bool
and x y = x && y

isEven :: Int -> Bool
isEven i = (mod i 2) == 0

sumTree :: Tree Int -> Int
sumTree tr = foldrTree plus 0 tr

andTree :: Tree Bool -> Bool
andTree tr = foldrTree and True tr

gibbon_main =
  let
    tr  = mkTree 10 1
    tr1 = fmapTree succ tr
    v1  = sumTree tr1
    tr2 = (fmapTree isEven tr1)
    v2  = andTree tr2
  in (v1, v2)

main :: IO ()
main = print gibbon_main
