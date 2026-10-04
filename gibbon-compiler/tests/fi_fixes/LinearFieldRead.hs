-- LinearFieldRead: List (Factored) with a PackedInt (Linear) field written inline
-- by mkList and read through unwrapP; the Linear buffer must advance per element.

module LinearFieldRead where

data PackedInt = PacI Int
{-# ANN type PackedInt "Linear" #-}

data List = Cons Int PackedInt List | Nil
{-# ANN type List "Factored" #-}

unwrapP :: PackedInt -> Int
unwrapP a = case a of
  PacI a2 -> a2

mkList :: Int -> List
mkList n = if n <= 0 then Nil else Cons n (PacI n) (mkList (n - 1))

sumList :: List -> Int
sumList l = case l of
  Nil -> 0
  Cons j i rst -> j + unwrapP i + sumList rst

gibbon_main = sumList (mkList 100)
