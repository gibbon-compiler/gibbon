-- RightTree: Tree (Factored).  right returns a field of its argument, a factored
-- indirection to it; sumTree reads through it.

module RightTree where

data Tree = Leaf Int | Node Tree Tree
{-# ANN type Tree "Factored" #-}

mkTree :: Int -> Int -> Tree
mkTree k n = if n <= 0 then Leaf k else Node (mkTree (k * 2) (n - 1)) (mkTree ((k * 2) + 1) (n - 1))

right :: Tree -> Tree
right t = case t of
  Leaf x -> Leaf x
  Node a b -> b

sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> x
  Node a b -> sumTree a + (2 * sumTree b)

gibbon_main = sumTree (right (mkTree 1 5))
