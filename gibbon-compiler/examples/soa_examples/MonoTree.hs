-- test monomorphic things
module MonoTree where

data Tree = Leaf Int
          | Node Int Tree Tree
  deriving Show

mkTree :: Int -> Tree
mkTree d =
  if d == 0
  then Leaf 1
  else Node d (mkTree (d-1)) (mkTree (d-1))

add1Tree :: Tree -> Tree
add1Tree t =
  case t of
    Leaf x -> Leaf (x + 1)
    Node d x1 x2 -> Node (d + 1) (add1Tree x1) (add1Tree x2)

sumTree :: Tree -> Int
sumTree tr =
  case tr of
    Leaf n    -> n
    Node d l r -> d + (sumTree l) + (sumTree r)

gibbon_main = sumTree (mkTree 18) --sumTree (add1Tree (mkTree 18))

main :: IO ()
main = print gibbon_main
