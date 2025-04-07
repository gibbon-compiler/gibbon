module Tree where

data Tree = Leaf Int Float
          | Node Int Float Tree Tree Tree
  deriving Show

mkTree :: Int -> Tree
mkTree d =
  if d == 0
  then Leaf d 0.0
  else Node d 0.0 (mkTree (d-1)) (mkTree (d-1)) (mkTree (d-1))

add1Tree :: Tree -> Tree
add1Tree t =
  case t of
    Leaf x y -> Leaf (x + 1) y
    Node i j x1 x2 x3 -> Node (i + 1) j (add1Tree x1) (add1Tree x2) (add1Tree x3) 

rightmost :: Tree -> Int
rightmost tree = case tree of 
		      Leaf i _ -> i
                      Node _ _ l r rr -> rightmost rr

sumTree :: Tree -> Int
sumTree tr =
  case tr of
    Leaf n m   -> n
    Node i _ l r rr -> i + (sumTree l) + (sumTree r) + (sumTree rr)

gibbon_main = 
   let tree = mkTree 15
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
     in ()
