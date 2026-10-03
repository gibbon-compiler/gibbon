-- MixedLayout: List (Factored) with a PackedInt (Linear) field.  idList shares
-- the list through a factored indirection one of whose buffers is Linear.

module MixedLayout where

data PackedInt = PacI Int
{-# ANN type PackedInt "Linear" #-}

data List = Cons Int PackedInt List | Nil
{-# ANN type List "Factored" #-}

bumpP :: PackedInt -> Int -> PackedInt
bumpP a b = case a of
  PacI a' -> PacI (a' + b)

unwrapP :: PackedInt -> Int
unwrapP a = case a of
  PacI a' -> a'

mkList :: Int -> List
mkList n = if n <= 0 then Nil else Cons n (PacI n) (mkList (n - 1))

add1 :: List -> List
add1 l = case l of
  Nil -> Nil
  Cons j i rst -> Cons (j + 1) (bumpP i 1) (add1 rst)

sumList :: List -> Int
sumList l = case l of
  Nil -> 0
  Cons j i rst -> j + unwrapP i + sumList rst

idList :: List -> List
idList l = l

gibbon_main = sumList (idList (add1 (mkList 100)))
