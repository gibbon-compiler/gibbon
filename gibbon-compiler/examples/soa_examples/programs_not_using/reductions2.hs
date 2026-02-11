data List = Cons Int List | Nil
{-# ANN type List "Factored" #-} 

mkList :: Int -> List
mkList len = if len <= 0
             then Nil
             else
              let rst = mkList (len - 1)
              in Cons len rst

reduce :: List -> Int
reduce lst = case lst of
                  Nil -> 0
                  Cons a rst -> a + reduce rst

gibbon_main =
    let lst = mkList 1000000
        sum_a = iterate (reduce lst)
     in sum_a
