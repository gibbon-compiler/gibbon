-- TraverseThenRead: g, a non-recursive function, skips the left subtree with a
-- traversal and then reads the right one.

module TraverseThenRead where
data Tree = Leaf Int | Node Tree Tree
{-# ANN type Tree "Factored" #-}
mkTree :: Int -> Int -> Tree
mkTree k n = if n <= 0 then Leaf k else Node (mkTree (k * 2) (n - 1)) (mkTree ((k * 2) + 1) (n - 1))
sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> x
  Node a b -> sumTree a + (2 * sumTree b)
g :: Tree -> Int
g t = case t of
  Leaf x -> x
  Node a b -> sumTree b
gibbon_main = g (mkTree 1 14)
