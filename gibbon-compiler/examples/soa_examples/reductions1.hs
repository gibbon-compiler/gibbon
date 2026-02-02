-- data A = CA Int A | ANil
data List = Cons Int Int Int Int Int Int Int Int Int Int List | Nil
{-# ANN type List "Linear" #-}
-- {-# ANN type A "Linear" #-}


-- mkA :: Int -> A
-- mkA len = if len <= 0
--           then ANil
--           else CA len (mkA (len - 1))

mkList :: Int -> List
mkList len = if len <= 0
             then Nil
             else
                let rst = mkList (len - 1)
                    in Cons len len len len len len len len len len rst

reduce :: List -> Int
reduce lst = case lst of
                  Nil -> 0
                  Cons a b c d e f g h i j rst -> a + reduce rst

id :: lst -> lst 
id l = l

gibbon_main =
    let lst = mkList 1000000
        sum_a = iterate (reduce lst)
     in sum_a
