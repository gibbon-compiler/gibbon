-- LinearFieldGrows: List (Factored) with a two-word PackedInt (Linear) field written
-- inline by mkList, enough elements that the Linear buffer needs many chunks.

module LinearFieldGrows where
data PackedInt = PacI Int Int
{-# ANN type PackedInt "Linear" #-}
data List = Cons Int PackedInt List | Nil
{-# ANN type List "Factored" #-}
unwrapP :: PackedInt -> Int
unwrapP a = case a of
  PacI a2 b2 -> (1000 * a2) + b2
mkList :: Int -> List
mkList n = if n <= 0 then Nil else Cons n (PacI n (n * 7)) (mkList (n - 1))
sumList :: List -> Int
sumList l = case l of
  Nil -> 0
  Cons j i rst -> j + unwrapP i + sumList rst
gibbon_main = sumList (mkList 3000)
