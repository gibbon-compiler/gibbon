-- LinearListReduction: List (Linear).
-- Functions: mkList, reduce, maxI, maxField, countHeavy, sumThird,
-- bumpFirst, shiftTriple, touchMost.
-- Annotated: MayVectorize on bumpFirst, shiftTriple, touchMost.
data List = Cons Int64 Int64 Int64 Int64 Int64 Int64 Int64 Int64 Int64 Int64 List | Nil

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


maxI :: Int -> Int -> Int
maxI a b = if a > b then a else b


-- Reads one scalar buffer of ten: the largest value in field g.
maxField :: List -> Int
maxField lst = case lst of
                    Nil -> 0
                    Cons _ _ _ _ _ _ g _ _ _ rst -> maxI g (maxField rst)


-- A filter expressed as a count: how many nodes hold a value above the
-- threshold in field e, without materializing the selected sublist.
countHeavy :: List -> Int -> Int
countHeavy lst t = case lst of
                    Nil -> 0
                    Cons _ _ _ _ e _ _ _ _ _ rst ->
                      let hit = if e > t then 1 else 0
                      in hit + countHeavy rst t


-- Sums field c, the field shiftTriple rewrites.
sumThird :: List -> Int
sumThird lst = case lst of
                    Nil -> 0
                    Cons _ _ c _ _ _ _ _ _ _ rst -> c + sumThird rst

{-# ANN bumpFirst "OPT:MayVectorize" #-}
-- Rewrites one field of ten, leaving ten of the eleven buffers untouched.
bumpFirst :: List -> Int -> List
bumpFirst lst k = case lst of
                    Nil -> Nil
                    Cons a b c d e f g h i j rst ->
                      Cons (a + k) b c d e f g h i j (bumpFirst rst k)

{-# ANN shiftTriple "OPT:MayVectorize" #-}
-- Rewrites three fields, leaving eight buffers untouched.
shiftTriple :: List -> List
shiftTriple lst = case lst of
                    Nil -> Nil
                    Cons a b c d e f g h i j rst ->
                      Cons a b (c + 3) (d - 1) (e + e) f g h i j (shiftTriple rst)

{-# ANN touchMost "OPT:MayVectorize" #-}
-- Rewrites eight fields, leaving three buffers untouched: the case where
-- there is little left for buffer sharing to share.
touchMost :: List -> List
touchMost lst = case lst of
                    Nil -> Nil
                    Cons a b c d e f g h i j rst ->
                      Cons (a + 1) (b + 2) (c + 3) (d + 4) (e + 5) (f + 6)
                           (g + 7) (h + 8) i j (touchMost rst)


gibbon_main = let _ = printsym (quote "Running program recution on List with 10 Integer elements: ")
                  _ = printsym (quote "NEWLINE")
                  lst = mkList 10000000

                  _ = printsym (quote "Running pass reduction (fold, uses=2): ")
                  _ = printsym (quote "NEWLINE")
                  sum = iterate (reduce lst)
                  _ = printsym (quote "End")
                  _ = printsym (quote "NEWLINE")
                  _ = printsym (quote "Running pass maxField (fold, uses=2): ")
                  _ = printsym (quote "NEWLINE")
                  peak = iterate (maxField lst)
                  _ = printsym (quote "End")
                  _ = printsym (quote "NEWLINE")
                  _ = printsym (quote "Running pass countHeavy (fold, uses=2): ")
                  _ = printsym (quote "NEWLINE")
                  heavy = iterate (countHeavy lst 32)
                  _ = printsym (quote "End")
                  _ = printsym (quote "NEWLINE")
                  _ = printsym (quote "Running pass bumpFirst (map, uses=11, shared=10): ")
                  _ = printsym (quote "NEWLINE")
                  lst' = iterate (bumpFirst lst 7)
                  _ = printsym (quote "End")
                  _ = printsym (quote "NEWLINE")
                  bumped = reduce lst'
                  _ = printsym (quote "Running pass shiftTriple (map, uses=11, shared=8): ")
                  _ = printsym (quote "NEWLINE")
                  lst'' = iterate (shiftTriple lst)
                  _ = printsym (quote "End")
                  _ = printsym (quote "NEWLINE")
                  shifted = sumThird lst''
                  _ = printsym (quote "Running pass touchMost (map, uses=11, shared=3): ")
                  _ = printsym (quote "NEWLINE")
                  lst' = iterate (touchMost lst)
                  _ = printsym (quote "End")
                  _ = printsym (quote "NEWLINE")
                  touched = reduce lst'
              in (sum, peak, heavy, bumped, shifted, touched)
