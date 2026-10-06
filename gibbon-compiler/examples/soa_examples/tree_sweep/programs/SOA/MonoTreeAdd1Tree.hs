-- MonoTreeAdd1Tree: Tree (Factored).
-- MonoTree with only its add1Tree pass, for the --tree-sweep, which
-- times it at every depth in a range. The depth is the executable's
-- --size-param, so one build serves every depth. The answer is the sum of
-- add1Tree's output, 2^d * (d(d+1)/2 + 1), computed after the timed pass.
-- Functions: mkTree, add1Tree, sumTree, main.
-- Annotated: MayVectorize on add1Tree; StoreScalarCounts on mkTree.
module MonoTreeAdd1Tree where

data Tree = Leaf Int64
          | Node Tree Tree
  deriving Show

{-# ANN type Tree "Factored" #-}
{-# ANN mkTree "OPT:StoreScalarCounts" #-}

mkTree :: Int -> Int -> Tree
mkTree d acc =
  if d == 0
  then Leaf acc
  else Node (mkTree (d-1) (d+acc)) (mkTree (d-1) (d+acc))

{-# ANN add1Tree "OPT:MayVectorize" #-}
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

gibbon_main = let 
                _ = printsym (quote "Running program MonoTreeAdd1Tree: ")
                _ = printsym (quote "NEWLINE")
                tree = (mkTree sizeParam 0)

                _ = printsym (quote "Running pass add1Tree (map, uses=3, shared=0): ")
                _ = printsym (quote "NEWLINE")
                tree' = iterate (add1Tree tree)
                _ = printsym (quote "End")
                _ = printsym (quote "NEWLINE")
              in sumTree tree'

main :: IO ()
main = print gibbon_main
