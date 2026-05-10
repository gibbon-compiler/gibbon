data A = CA Int A | ANil
data List = Cons Int Int Int Int Int Int Int Int Int Int A List | Nil
{-# ANN type List "Factored" #-}
{-# ANN type A "Linear" #-} 


mkA :: Int -> A 
mkA len = if len <= 0
          then ANil 
          else CA len (mkA (len - 1))

mkList :: Int -> List
mkList len = if len <= 0
             then Nil
             else
              let a = mkA 5000
                  rst = mkList (len - 1)
              in Cons len len len len len len len len len len a rst

reduce :: List -> Int
reduce lst = case lst of
                  Nil -> 0
                  Cons a b c d e f g h i j k rst -> a + reduce rst

gibbon_main =
    let lst = mkList 1000000
        sum_a = iterate (reduce lst)
     in sum_a
