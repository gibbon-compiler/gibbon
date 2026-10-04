-- LinearShareInList: a Linear list whose elements hold trees; bump rebuilds the list
-- and shares each tree through an indirection.  The trees span several chunks.

module LinearShareInList where

data Tree = Leaf Int | Node Tree Tree
{-# ANN type Tree "Linear" #-}

data TL = Nil | Cons Int Tree TL
{-# ANN type TL "Linear" #-}

mkTree :: Int -> Int -> Tree
mkTree k n = if n <= 0 then Leaf k else Node (mkTree (k * 2) (n - 1)) (mkTree ((k * 2) + 1) (n - 1))

mkTL :: Int -> TL
mkTL n = if n <= 0 then Nil else Cons n (mkTree n (mod n 4)) (mkTL (n - 1))

bump :: TL -> TL
bump l = case l of
  Nil -> Nil
  Cons x t rst -> Cons (x + 1) t (bump rst)

sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> mod x 1000
  Node a b -> sumTree a + (3 * sumTree b)

sumTL :: TL -> Int
sumTL l = case l of
  Nil -> 0
  Cons x t rst -> mod ((7 * x) + sumTree t + (5 * sumTL rst)) 1000000007

gibbon_main = sumTL (bump (bump (mkTL 6000)))
