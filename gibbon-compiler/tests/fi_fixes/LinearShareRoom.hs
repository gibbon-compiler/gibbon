-- LinearShareRoom: f shares each right subtree through an indirection written
-- after the recursive call, so a left spine writes indirections back to back.

module LinearShareRoom where

data Tree = Leaf Int | Node Tree Tree
{-# ANN type Tree "Linear" #-}

data TL = Nil | Cons Tree TL
{-# ANN type TL "Linear" #-}

leaf :: Int -> Tree
leaf x = Leaf x

mkL :: Int -> Tree
mkL d = if d <= 0 then Leaf 1 else Node (mkL (d - 1)) (leaf d)

mkTL :: Int -> TL
mkTL n = if n <= 0 then Nil else Cons (mkL (mod n 7)) (mkTL (n - 1))

f :: Tree -> Tree
f t = case t of
  Leaf x -> Leaf (x + 1)
  Node a b -> Node (f a) b

fl :: TL -> TL
fl l = case l of
  Nil -> Nil
  Cons t rst -> Cons (f t) (fl rst)

sumTree :: Tree -> Int
sumTree t = case t of
  Leaf x -> x
  Node a b -> sumTree a + (3 * sumTree b)

sumTL :: TL -> Int
sumTL l = case l of
  Nil -> 0
  Cons t rst -> mod (sumTree t + (5 * sumTL rst)) 1000000007

gibbon_main = sumTL (fl (mkTL 20000))
