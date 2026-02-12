-- @BENCH adt_fields=11
data List = Cons Int Int Int Int Int Int Int Int Int Int List | Nil

{-# ANN type List "Linear" #-}

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


gibbon_main = let _ = printsym (quote "Running program recution on List with 10 Integer elements: ")
                  _ = printsym (quote "NEWLINE")
                  lst = mkList 10000000
                  _ = printsym (quote "Running pass reduction (fold, uses=2): ")
                  _ = printsym (quote "NEWLINE")
                  sum = iterate (reduce lst)
                  _ = printsym (quote "End")
                  _ = printsym (quote "NEWLINE")
              in sum
