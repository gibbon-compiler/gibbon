{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE BangPatterns #-}
module Main where
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Prelude hiding (iterate)
import GibbonCompat

module Tree where
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

-- @BENCH adt_fields=5
data Tree = Leaf Int
          | Node Int Tree Tree Tree
  deriving Show

{-# ANN type Tree "Linear" #-}

mkTree :: Int -> Tree
mkTree d =
  if d == 0
  then Leaf d
  else Node 1 (mkTree (d-1)) (mkTree (d-1)) (mkTree (d-1))

add1Tree :: Tree -> Tree
add1Tree t =
  case t of
    Leaf x -> Leaf (x + 1)
    Node i x1 x2 x3 -> Node (i + 1) (add1Tree x1) (add1Tree x2) (add1Tree x3)

rightmost :: Tree -> Int
rightmost tree = case tree of
                      Leaf i -> i
                      Node a l r ll -> rightmost ll

sumTree :: Tree -> Int
sumTree tr =
  case tr of
    Leaf n -> n
    Node i l r ll -> i + (sumTree l) + (sumTree r) + (sumTree ll)

id :: Tree -> Tree 
id tree = tree


gibbon_main = do
  _ <- printsymIO (quote "Running program Ternary Heap: ")
  _ <- printsymIO (quote "NEWLINE")
  let tree = mkTree 15
  _ <- printsymIO (quote "Running pass add 1 tree (map, uses=5): ")
  _ <- printsymIO (quote "NEWLINE")
  tree' <- iterateIO (\() -> add1Tree tree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass sum tree (fold, uses=5): ")
  _ <- printsymIO (quote "NEWLINE")
  sum <- iterateIO (\() -> sumTree tree')
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  return (sum)

main = runGibbonMainIO gibbon_main

instance NFData Tree
