{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE BangPatterns #-}
module Main where
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Prelude hiding (iterate)
import GibbonCompat

-- @BENCH adt_fields=11
data List = Cons Int Int Int Int Int Int Int Int Int Int List | Nil
  deriving (Generic)

{-# ANN type List "Linear" #-}

mkList :: Int -> List
mkList len = if len < 0
             then Nil
             else let
                    rst = mkList (len - 1)
                  in Cons len len len len len len len len len len rst


reduce :: List -> Int
reduce lst = case lst of
                    Nil -> 0
                    Cons a b c d e f g h i j rst -> let sumRst = reduce rst
                                                        in a + sumRst



gibbon_main = do
  _ <- printsymIO (quote "NEWLINE")
  let lst = mkList 10000000
  _ <- printsymIO (quote "Running pass reduction (fold, uses=2): ")
  _ <- printsymIO (quote "NEWLINE")
  sum <- iterateIO (\() -> reduce lst)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  return (sum)

main = runGibbonMainIO gibbon_main

instance NFData List
