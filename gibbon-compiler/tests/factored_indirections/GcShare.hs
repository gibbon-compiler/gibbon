-- GcShare: Tree (Factored).  A value holding factored indirections stays live
-- while churn allocates and frees many regions.

module GcShare where

data Tree = Leaf Int | Node Tree Tree
{-# ANN type Tree "Factored" #-}

mkTree :: Int -> Int -> Tree
mkTree k n = if n <= 0 then Leaf k else Node (mkTree (k * 2) (n - 1)) (mkTree ((k * 2) + 1) (n - 1))

f :: Tree -> Tree
f t = case t of
  Leaf x -> Leaf (x + 1)
  Node a b -> Node (f a) b

sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> mod x 1000
  Node a b -> sumTree a + (3 * sumTree b)

churn :: Int -> Int -> Int
churn i acc = if i <= 0 then acc
              else churn (i - 1) (mod (acc + sumTree (f (mkTree i 10))) 1000000007)

gibbon_main =
  let t = f (mkTree 1 12)
      c = churn 200 0
  in (c, sumTree t, sumTree (f t))
