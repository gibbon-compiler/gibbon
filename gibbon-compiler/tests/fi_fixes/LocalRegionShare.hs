-- LocalRegionShare: mkShared builds a tree in a region local to it and maps it
-- into its output; both values' starts must survive the mutable calls.

module LocalRegionShare where

data Tree = Leaf Int | Node Tree Tree
{-# ANN type Tree "Factored" #-}

mkTree :: Int -> Int -> Tree
mkTree k n = if n <= 0 then Leaf k else Node (mkTree (k * 2) (n - 1)) (mkTree ((k * 2) + 1) (n - 1))

f :: Tree -> Tree
f t = case t of
  Leaf x -> Leaf (x + 1)
  Node a b -> Node (f a) (f b)

-- The tree f shares from lives in a region local to this function.
mkShared :: Int -> Tree
mkShared n = f (mkTree n 12)

sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> mod x 1000
  Node a b -> sumTree a + (3 * sumTree b)

gibbon_main =
  let t = mkShared 1 in
  let a = sumTree (mkTree 5 15) in
  let b = sumTree (mkTree 6 15) in
  (a + b, sumTree t)
