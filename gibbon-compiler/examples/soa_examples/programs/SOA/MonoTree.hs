-- test monomorphic things
module MonoTree where

-- @BENCH adt_fields=3
data Tree = Leaf Int
          | Node Tree Tree
  deriving Show

{-# ANN type Tree "Factored" #-}

mkTree :: Int -> Int -> Tree
mkTree d acc =
  if d == 0
  then Leaf (acc)
  else Node (mkTree (d-1) (d+acc)) (mkTree (d-1) (d+acc))

add1Tree :: Tree -> Tree
add1Tree t =
  case t of
    Leaf x -> Leaf (x + 1)
    Node x1 x2 -> Node (add1Tree x1) (add1Tree x2)

sumTree :: Tree -> Int
sumTree tr =
  case tr of
    Leaf n    -> n
    Node l r -> (sumTree l) + (sumTree r)

sumTreeAcc :: Tree -> Int -> Int
sumTreeAcc t acc =
  case t of
    Leaf n ->
      acc + n
    Node l r ->
      let acc1 = sumTreeAcc l acc
      in sumTreeAcc r acc1

id :: Tree -> Tree 
id tree = tree

gibbon_main = let 
                _ = printsym (quote "Running program MonoTree: ")
                _ = printsym (quote "NEWLINE")
                tree = (mkTree 23 0)
                _ = printsym (quote "Running pass add1Tree (map, uses=3): ")
                _ = printsym (quote "NEWLINE")
                tree' =  iterate (add1Tree tree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass sumTree (fold, uses=3): ")
                _ = printsym (quote "NEWLINE")
                val = iterate (sumTree tree')
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass sumTree TailRec (fold, uses=3): ")
                _ = printsym (quote "NEWLINE")
                val' = iterate (sumTreeAcc tree' 0)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
              in (val, val')

main :: IO ()
main = print gibbon_main
