-- test monomorphic things
module MonoTree where

data Tree = Leaf Int Float
          | Node Int Float Tree Tree
  deriving Show

mkTree :: Int -> Tree
mkTree d =
  if d == 0
  then Leaf 1 1.0
  else Node d 1.0 (mkTree (d-1)) (mkTree (d-1))

--add1Tree :: Tree -> Tree
--add1Tree t =
--  case t of
--    Leaf x y -> Leaf (x + 1) y
--    Node i j x1 x2 -> Node (i + 1) j (add1Tree x1) (add1Tree x2)

sumTree :: Tree -> Int
sumTree tr =
  case tr of
    Leaf n m   -> n
    Node i _ l r -> i + (sumTree l) + (sumTree r)

gibbon_main = 
   let tree = mkTree 5
       _ = printPacked tree
       --tree' = add1Tree tree 
       --_ =  printPacked tree'
       val = sumTree tree 
     in printint val


-- sumTree (add1Tree (mkTree 10))

--main :: IO ()
--main = print gibbon_main
