-- LinearShareChunks: f and swapT share subtrees through indirections that
-- point into earlier chunks of a region and into other regions.

module LinearShareChunks where

data Tree = Leaf Int | Node Tree Tree
{-# ANN type Tree "Linear" #-}

mkTree :: Int -> Int -> Tree
mkTree k n = if n <= 0 then Leaf k else Node (mkTree (k * 2) (n - 1)) (mkTree ((k * 2) + 1) (n - 1))

idTree :: Tree -> Tree
idTree t = t

f :: Tree -> Tree
f t = case t of
  Leaf x -> Leaf (x + 1)
  Node a b -> Node (f a) b

swapT :: Tree -> Tree
swapT t = case t of
  Leaf x -> Leaf x
  Node a b -> Node (swapT b) a

sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> mod x 1000
  Node a b -> sumTree a + (3 * sumTree b)

gibbon_main =
  let t = mkTree 1 17
  in (sumTree (idTree t), sumTree (f (f t)), sumTree (swapT (swapT t)))
