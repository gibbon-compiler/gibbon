-- test monomorphic things
module MonoTree where

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

--gibbon_main = iterate (sumTree (add1Tree (mkTree 23)))

--main :: IO ()
--main = print gibbon_main

gibbon_main = 
	let tree = mkTree 23
            --_ = printPacked tree 
            tree' = iterate (add1Tree tree) 
            sum = sumTree tree' 
         in sum

