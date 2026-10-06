-- MonoTreeSumTree: Tree (Linear).
-- MonoTree with only its sumTree pass, for the --sumtree-size-sweep, which
-- times it at every depth in a range. The depth is the executable's
-- --size-param, so one build serves every depth; mkTree d 0 gives every one
-- of its 2^d leaves the value d(d+1)/2, so sumTree returns 2^d * d(d+1)/2.
-- Functions: mkTree, sumTree, main.
module MonoTreeSumTree where

data Tree = Leaf Int64
          | Node Tree Tree
  deriving Show

{-# ANN type Tree "Linear" #-}

mkTree :: Int -> Int -> Tree
mkTree d acc =
  if d == 0
  then Leaf acc
  else Node (mkTree (d-1) (d+acc)) (mkTree (d-1) (d+acc))

sumTree :: Tree -> Int
sumTree tr =
  case tr of
    Leaf n    -> n
    Node l r -> (sumTree l) + (sumTree r)

gibbon_main = let 
                _ = printsym (quote "Running program MonoTreeSumTree: ")
                _ = printsym (quote "NEWLINE")
                tree = (mkTree sizeParam 0)

                _ = printsym (quote "Running pass sumTree (fold, uses=3): ")
                _ = printsym (quote "NEWLINE")
                val = iterate (sumTree tree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
              in val

main :: IO ()
main = print gibbon_main
