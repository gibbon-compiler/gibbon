module Tree where

data Tree = Leaf Int Float
          | Node Int Int Int Float Tree Tree Tree Tree
  deriving Show
{-# ANN type Tree "Factored" #-}

mkTree :: Int -> Tree
mkTree d =
  if d == 0
  then Leaf d 0.0
  else Node d (d - 1) (d + 1) 0.0 (mkTree (d-1)) (mkTree (d-1)) (mkTree (d-1)) (mkTree (d-1))

add1Tree :: Tree -> Tree
add1Tree t =
  case t of
    Leaf x y -> Leaf (x + 1) y
    Node i j k l x1 x2 x3 x4 -> Node (i + 1) (j + 1) (k + 1) l (add1Tree x1) (add1Tree x2) (add1Tree x3) (add1Tree x4) 

rightmost :: Tree -> Int
rightmost tree = case tree of 
		      Leaf i _ -> i
                      Node _ _ _ _ l r ll rr -> rightmost rr

sumTree :: Tree -> Int
sumTree tr =
  case tr of
    Leaf n m   -> n
    Node i j k _ l r ll rr -> i + j + k + (sumTree l) + (sumTree r) + (sumTree ll) + (sumTree rr)

gibbon_main = 
   let tree = mkTree 10
       -- _ = printPacked tree
       tree' = add1Tree tree 
       --_ =  printPacked tree'
       val = sumTree tree'
       _ = printsym (quote "\n\n(sum: ")
       _ = printint val 
       _ = printsym (quote ", rightmost: ")
       rmost = rightmost tree'
       _ = printint rmost
       _ = printsym (quote ")\n\n")
     in sumTree tree'
