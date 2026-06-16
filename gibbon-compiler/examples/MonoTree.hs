-- test monomorphic things
module MonoTree where

{-# ANN type Tree "Factored" #-}

data Tree = Leaf Int
          | Node Tree Tree
  deriving Show

mkTree :: Int -> Tree
mkTree d =
  if d == 0
  then Leaf 1
  else Node (mkTree (d-1)) (mkTree (d-1))

add1Tree :: Tree -> Tree
add1Tree t =
  case t of
    Leaf x     -> Leaf (x + 1)
    Node x1 x2 -> Node (add1Tree x1) (add1Tree x2)

sumTree :: Tree -> Int
sumTree tr =
  case tr of
    Leaf n   -> n
    Node l r -> (sumTree l) + (sumTree r)

rightMost :: Tree -> Int
rightMost tr =
  case tr of 
    Leaf n -> n
    Node l r -> (rightMost r)

gibbon_main = rightMost (add1Tree (mkTree 20))

main :: IO ()
main = print gibbon_main
