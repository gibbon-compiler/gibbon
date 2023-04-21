module BinTree where

import Gibbon.Plugin ( PackedAnn(..) )

data Tree a = Leaf Int a
            | Node Int (Tree a) (Tree a)

{-# ANN mkTree_seq LiftPacked #-}
mkTree_seq :: Int -> Tree Bool
mkTree_seq i =
  if i <= 0
  then Leaf 1 True
  else
      let x = mkTree_seq (i-1)
          y = mkTree_seq (i-1)
      in Node i x y

{-# ANN sumTree_seq LiftPacked #-}
sumTree_seq :: Tree a -> Int
sumTree_seq foo =
  case foo of
    Leaf i _   -> i
    Node _ a b ->
      let x = sumTree_seq a
          y = sumTree_seq b
      in x + y

{-# ANN bench1 LiftPacked #-}
bench1 :: Int -> Int
bench1 n = sumTree_seq (mkTree_seq n)
