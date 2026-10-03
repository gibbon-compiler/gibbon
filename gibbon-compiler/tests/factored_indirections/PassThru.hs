-- PassThru: Tree (Factored).  f rebuilds the left spine and shares each right
-- child through a factored indirection written after the rebuilt left child.

module PassThru where

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
  Leaf x -> x
  Node a b -> sumTree a + (3 * sumTree b)

gibbon_main = sumTree (f (f (mkTree 1 6)))
