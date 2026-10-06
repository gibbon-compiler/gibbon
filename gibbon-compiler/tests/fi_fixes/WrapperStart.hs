-- WrapperStart: wrap, a non-recursive (immutable-convention) function, builds
-- its result with a mutable-convention writer; the value's start must survive.

module WrapperStart where
data Tree = Leaf Int | Node Tree Tree
{-# ANN type Tree "Factored" #-}
mkTree :: Int -> Int -> Tree
mkTree k n = if n <= 0 then Leaf k else Node (mkTree (k * 2) (n - 1)) (mkTree ((k * 2) + 1) (n - 1))
wrap :: Int -> Tree
wrap n = mkTree n 10
sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> mod x 1000
  Node a b -> sumTree a + (3 * sumTree b)
gibbon_main = sumTree (wrap 1)
