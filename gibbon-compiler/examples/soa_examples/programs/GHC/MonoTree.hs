{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE BangPatterns #-}
module Main where
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Prelude hiding (iterate)
import GibbonCompat

-- test monomorphic things
module MonoTree where
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

-- @BENCH adt_fields=3
data Tree = Leaf Int
          | Node Tree Tree
  deriving Show

{-# ANN type Tree "Linear" #-}

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


gibbon_main = do
  _ <- printsymIO (quote "Running program MonoTree: ")
  _ <- printsymIO (quote "NEWLINE")
  let tree = (mkTree 23 0)
  _ <- printsymIO (quote "Running pass add1Tree (map, uses=3): ")
  _ <- printsymIO (quote "NEWLINE")
  tree' <- iterateIO (\() -> add1Tree tree)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass sumTree (fold, uses=3): ")
  _ <- printsymIO (quote "NEWLINE")
  val <- iterateIO (\() -> sumTree tree')
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass sumTree TailRec (fold, uses=3): ")
  _ <- printsymIO (quote "NEWLINE")
  val' <- iterateIO (\() -> sumTreeAcc tree' 0)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  let main :: IO ()
  let main = print gibbon_main
  return ((val, val'))

main = runGibbonMainIO gibbon_main

instance NFData Tree
