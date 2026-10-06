{-# LANGUAGE BangPatterns #-}
-- CSE off so the two subtrees of a node are built separately, as every other
-- implementation builds them, rather than shared.
{-# OPTIONS_GHC -fno-cse #-}
-- MonoTree's three traversals for the tree sweep (gibbon_benchmark.py
-- --tree-sweep), ported from BintreeBench (ECOOP 2017, treebench.hs) and
-- aligned with tree_sweep/programs/*/MonoTree*.hs: strict 64-bit leaves,
-- mkTree d 0 gives every one of the 2^d leaves d(d+1)/2.
--
--   treebench <build|add1|sum> --size-param DEPTH --iterate N
--
-- prints each iteration's time in Gibbon's format, then the sum of the
-- result. Each iteration reads its input from an IORef, so the computation
-- cannot be floated out of the loop and done once.
module Main (main) where

import Control.Exception (evaluate)
import Control.Monad (forM)
import Data.Int (Int64)
import Data.IORef
import Data.List (intercalate)
import GHC.Clock (getMonotonicTimeNSec)
import System.Environment (getArgs)
import Text.Printf (printf)

data Tree = Leaf {-# UNPACK #-} !Int64 | Node !Tree !Tree

mkTree :: Int64 -> Int64 -> Tree
mkTree d acc
  | d == 0 = Leaf acc
  | otherwise = Node (mkTree (d - 1) (d + acc)) (mkTree (d - 1) (d + acc))

add1Tree :: Tree -> Tree
add1Tree (Leaf x) = Leaf (x + 1)
add1Tree (Node l r) = Node (add1Tree l) (add1Tree r)

sumTree :: Tree -> Int64
sumTree (Leaf x) = x
sumTree (Node l r) = sumTree l + sumTree r

arg :: String -> [String] -> Int
arg flag (f : v : rest) | f == flag = read v
                        | otherwise = arg flag (v : rest)
arg flag _ = error ("missing " ++ flag)

timed :: IO a -> IO (Double, a)
timed act = do
  t0 <- getMonotonicTimeNSec
  !r <- act
  t1 <- getMonotonicTimeNSec
  return (fromIntegral (t1 - t0) / 1e9, r)

main :: IO ()
main = do
  args <- getArgs
  let pass = head args
      depth = fromIntegral (arg "--size-param" args) :: Int64
      iters = max 1 (arg "--iterate" args)
  depthRef <- newIORef depth
  (header, results, answerOf) <- case pass of
    "build" -> do
      rs <- forM [1 .. iters] $ \_ ->
              timed (readIORef depthRef >>= \d -> evaluate (mkTree d 0))
      return ("buildTree (build)", map fst rs, sumTree (snd (last rs)))
    "add1" -> do
      tree <- evaluate (mkTree depth 0)
      ref <- newIORef tree
      rs <- forM [1 .. iters] $ \_ ->
              timed (readIORef ref >>= evaluate . add1Tree)
      return ("add1Tree (map)", map fst rs, sumTree (snd (last rs)))
    "sum" -> do
      tree <- evaluate (mkTree depth 0)
      ref <- newIORef tree
      rs <- forM [1 .. iters] $ \_ ->
              timed (readIORef ref >>= evaluate . sumTree)
      return ("sumTree (fold)", map fst rs, snd (last rs))
    _ -> error "pass must be build, add1 or sum"
  putStrLn ("Running pass " ++ header ++ ": ")
  putStrLn ("ITER TIMES: [" ++ intercalate ", " (map (printf "%.9f") results) ++ "]")
  putStrLn "End"
  print answerOf
