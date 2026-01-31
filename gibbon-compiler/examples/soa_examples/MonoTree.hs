-- test monomorphic things
module MonoTree where

data Tree = Leaf Int
          | Node Int Tree Tree
  deriving Show
{-# ANN type Tree "Linear" #-}

mkTree :: Int -> Int -> Tree
mkTree d acc =
  if d == 0
  then Leaf (acc)
  else Node d (mkTree (d-1) (d+acc)) (mkTree (d-1) (d+acc))

add1Tree :: Tree -> Tree
add1Tree t =
  case t of
    Leaf x -> Leaf (x + 1)
    Node d x1 x2 -> Node (d + 1) (add1Tree x1) (add1Tree x2)

rightMost :: Tree -> Int
rightMost t = case t of
                  Leaf x -> x
                  Node d x1 x2 -> rightMost x2

sumTree :: Tree -> Int
sumTree tr =
  case tr of
    Leaf n    -> n
    Node d l r -> d + (sumTree l) + (sumTree r)

id :: Tree -> Tree 
id tree = tree

gibbon_main = let 
                tree = (mkTree 22 0)
                --_ = printPacked tree
                --_ = printsym (quote "NEWLINE")
                tree' =  iterate ((add1Tree tree))
                val1 = iterate (sumTree tree)
                val = iterate (sumTree tree')
                rightmost = iterate (rightMost tree')
               in (val1, val, rightmost)

main :: IO ()
main = print gibbon_main
