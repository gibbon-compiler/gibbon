-- MonoTreeBuildTree: Tree (Linear).
-- MonoTree's construction alone, for the --tree-sweep, which times it at
-- every depth in a range. The depth is the executable's --size-param, so one
-- build serves every depth. The answer is the sum of the tree built last,
-- 2^d * d(d+1)/2, computed after the timed pass.
-- Functions: mkTree, sumTree, main.
module MonoTreeBuildTree where

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
                _ = printsym (quote "Running program MonoTreeBuildTree: ")
                _ = printsym (quote "NEWLINE")
                _ = printsym (quote "Running pass buildTree (build): ")
                _ = printsym (quote "NEWLINE")
                tree = iterate (mkTree sizeParam 0)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
              in sumTree tree

main :: IO ()
main = print gibbon_main
