-- IdTree: Tree (Factored).  idTree returns its argument, so its result is a
-- factored indirection to the input; sumTree reads through it.

module IdTree where

data Tree = Leaf Int | Node Tree Tree
{-# ANN type Tree "Factored" #-}

mkTree :: Int -> Tree
mkTree n = if n <= 0 then Leaf 1 else Node (mkTree (n - 1)) (mkTree (n - 1))

idTree :: Tree -> Tree
idTree t = t

sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> x
  Node a b -> sumTree a + sumTree b

gibbon_main = sumTree (idTree (mkTree 4))
