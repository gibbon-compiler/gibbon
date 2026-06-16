module Tree where


-- @BENCH adt_fields=5
data Tree = Leaf Int
          | Node Int Tree Tree Tree
  deriving Show

{-# ANN type Tree "Factored" #-}

{-# ANN mkTree "OPT:StoreScalarCounts" #-}
mkTree :: Int -> Tree
mkTree d =
  if d == 0
  then Leaf d
  else Node 1 (mkTree (d-1)) (mkTree (d-1)) (mkTree (d-1))

{-# ANN add1Tree "OPT:CanVectorize" #-}
add1Tree :: Tree -> Tree
add1Tree t =
  case t of
    Leaf x -> Leaf (x + 1)
    Node i x1 x2 x3 -> Node (i + 1) (add1Tree x1) (add1Tree x2) (add1Tree x3)

rightmost :: Tree -> Int
rightmost tree = case tree of
                      Leaf i -> i
                      Node a l r ll -> rightmost ll

sumTree :: Tree -> Int
sumTree tr =
  case tr of
    Leaf n -> n
    Node i l r ll -> i + (sumTree l) + (sumTree r) + (sumTree ll)

id :: Tree -> Tree 
id tree = tree

gibbon_main = 
   let _ = printsym (quote "Running program Ternary Heap: ")
       _ = printsym (quote "NEWLINE")
       tree = mkTree 15

       _ = printsym (quote "Running pass add 1 tree (map, uses=5): ")
       _ = printsym (quote "NEWLINE")
       tree' = iterate(add1Tree tree)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass sum tree (fold, uses=5): ")
       _ = printsym (quote "NEWLINE")
       sum = iterate(sumTree tree')
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass rightmost tree (fold, uses=2): ")
       rmv = iterate (rightmost tree)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
     in (sum, rmv)
