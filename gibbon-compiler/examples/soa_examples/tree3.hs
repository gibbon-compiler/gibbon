module Tree where

data Tree = Leaf Int
          | Node Int Tree Tree Tree
  deriving Show
{-# ANN type Tree "Factored" #-}

mkTree :: Int -> Tree
mkTree d =
  if d == 0
  then Leaf d
  else Node 1 (mkTree (d-1)) (mkTree (d-1)) (mkTree (d-1))

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
   let tree = id (mkTree 15)
       tree' = id (add1Tree tree)
       tree'' = id (add1Tree tree')
       --val = sumTree tree'
       --_ = printsym (quote "(sum: ")
       --_ = printint val 
       --_ = printsym (quote ", rightmost: ")
       rmost = (rightmost tree'')
       --_ = printint rmost
       --_ = printsym (quote ")\n\n")
     in sumTree tree'' --printPacked tree'' --rmost --()
