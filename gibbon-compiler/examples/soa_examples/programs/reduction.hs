data List = Cons Int Int Int Int Int Int Int Int Int Int List | Nil
{-# ANN type List "Factored" #-}

mkList :: Int -> List
mkList len = if len < 0
             then Nil
             else let
                    rst = mkList (len - 1)
                  in Cons len len len len len len len len len len rst


reduce :: List -> Int
reduce lst = case lst of
                    Nil -> 0
                    Cons a b c d e f g h e f rst -> let sumRst = reduce rst
                                                        in a + sumRst


gibbon_main = let lst = mkList 1000000
                  sum = iterate (reduce lst)
              in sum
