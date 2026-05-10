{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE BangPatterns #-}
module Main where
import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Prelude hiding (iterate, length, id)
import GibbonCompat

-- @BENCH adt_fields=2
data List = Cons Int List | Nil 
  deriving (Generic)

{-# ANN type List "Linear" #-}

mkList :: Int -> List 
mkList length = if length <= 0
		then Nil 
		else
		  let rst = mkList (length - 1) 
                   in Cons length rst 



add1 :: List -> List 
add1 lst = case lst of 
		Nil -> Nil 
		Cons i rst -> let 
				i1 = i + 1
			       in Cons i1 (add1 rst)
                                          

sumList :: List -> Int 
sumList lst = case lst of 
		   Nil -> 0
		   Cons i rst -> let sumRst = sumList rst 
                                  in i + sumRst

sumListAcc :: List -> Int -> Int
sumListAcc lst acc = case lst of
			   Nil -> acc
			   Cons i rst -> sumListAcc rst (acc + i)

lengthList :: List -> Int
lengthList lst = case lst of
		   Nil -> 0
                   Cons i rst -> 1 + (lengthList rst)

idList :: List -> List
idList lst = lst


gibbon_main = do
  _ <- printsymIO (quote "Running program List: ")
  _ <- printsymIO (quote "NEWLINE")
  let lst = mkList 100000000
  _ <- printsymIO (quote "Running pass add1 List (map, uses=2): ")
  _ <- printsymIO (quote "NEWLINE")
  lst' <- iterateIO (\() -> add1 lst)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass length List (fold, uses=1): ")
  _ <- printsymIO (quote "NEWLINE")
  len <- iterateIO (\() -> lengthList lst)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass sumList (fold, uses=2): ")
  _ <- printsymIO (quote "NEWLINE")
  sum <- iterateIO (\() -> sumList lst')
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  _ <- printsymIO (quote "Running pass sumList tail recursive (fold, uses=2): ")
  _ <- printsymIO (quote "NEWLINE")
  sum' <- iterateIO (\() -> sumListAcc lst' 0)
  _ <- printsymIO (quote "End")
  _ <- printsymIO (quote "NEWLINE")
  return ((sum, sum', len))

main = runGibbonMainIO gibbon_main

instance NFData List
