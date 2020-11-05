{-# LANGUAGE CPP            #-}
{-# LANGUAGE BangPatterns   #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}

module Main where

import Prelude hiding (iterate)
import Control.Exception
import Data.IORef
import Data.Maybe ( isJust )
import GHC.Generics (Generic)
import System.IO.Unsafe (unsafePerformIO)
import System.Environment

import Control.DeepSeq
import Data.Time.Clock
import qualified Data.Map as M

--------------------------------------------------------------------------------

type Sym = String

eqsym :: Sym -> Sym -> Bool
eqsym = (==)

quote = id
iterate = id
spawn = id
sync = ()
sizeParam = 1

printsym :: Sym -> ()
printsym s = unsafePerformIO (print s)

printint :: Int -> ()
printint i = unsafePerformIO (print i)

print_newline :: () -> ()
print_newline _ = unsafePerformIO (print "")

--------------------------------------------------------------------------------
-- Environments, using Data.Map

empty_int_hash = empty_hash
insert_int_hash = insert_hash
contains_int_hash = contains_hash

----------------------------------------

-- type SymHash = M.Map Sym Sym
-- type IntHash = M.Map Sym Int

-- empty_hash :: M.Map Sym a
-- empty_hash = M.empty

-- lookup_hash :: M.Map Sym Sym -> Sym -> Sym
-- lookup_hash env k = M.findWithDefault k k env

-- insert_hash :: M.Map Sym a -> Sym -> a -> M.Map Sym a
-- insert_hash env k v = M.insert k v env

-- contains_hash :: M.Map Sym a -> Sym -> Bool
-- contains_hash env k = M.member k env

-- lookup_int_hash :: M.Map Sym Int -> Sym -> Int
-- lookup_int_hash env k = M.findWithDefault 0 k env

----------------------------------------

-- Environments, using lists

type SymHash = [(Sym,Sym)]
type IntHash = [(Sym, Int)]

empty_hash :: [(Sym,a)]
empty_hash = []

lookup_hash :: [(Sym,Sym)] -> Sym -> Sym
lookup_hash env k = lookupWithDefault0 k k env

insert_hash :: [(Sym,a)] -> Sym -> a -> [(Sym,a)]
insert_hash env k v = (k, v) : env

contains_hash :: [(Sym,a)] -> Sym -> Bool
contains_hash env k = isJust (lookup k env)

lookup_int_hash :: [(Sym,Int)] -> Sym -> Int
lookup_int_hash env k = lookupWithDefault0 0 k env

lookupWithDefault0 ::  Eq a => b -> a -> [(a, b)] -> b
lookupWithDefault0 def k ls =
  case lookup k ls of
    Nothing -> def
    Just v  -> v

--------------------------------------------------------------------------------

type List a = [a]

alloc_ll = []
cons_ll x xs = x : xs
head_ll (x:_) = x
tail_ll (_:xs) = xs
is_empty_ll ls = null ls
append_ll xs ys = xs ++ ys

ifoldl_ll :: (b -> Int -> a -> b) -> b -> List a -> b
{-# INLINE ifoldl_ll #-}
ifoldl_ll f acc ls = ifoldl_ll_loop 0 f acc ls

ifoldl_ll_loop :: Int -> (b -> Int -> a -> b) -> b -> List a -> b
ifoldl_ll_loop idx f acc ls =
  if is_empty_ll ls
  then acc
  else
    let hd = head_ll ls
        tl = tail_ll ls
    in ifoldl_ll_loop (idx+1) f (f acc idx hd) tl

--------------------------------------------------------------------------------

-- broken
global_gensym_counter :: IORef Int
global_gensym_counter = unsafePerformIO (newIORef 0)

-- broken
gensym :: Sym
gensym = unsafePerformIO
  ( do modifyIORef' global_gensym_counter (\i -> i+1)
       i <- readIORef global_gensym_counter
       pure (show i)
  )

--------------------------------------------------------------------------------

#include "../Compiler.hs"

main :: IO ()
main = do
  args <- getArgs
  case args of
    [size] -> do
      let n = (read size) :: Int
      let ex = (make_big_ex n 0)
      let !prg = force $ (ProgramA intTy ex)
      start <- getCurrentTime
      !compiled <- pure $ force $ compile2 prg
      end <- getCurrentTime
      -- print compiled
      let runningTime = ((fromRational $ toRational $ diffUTCTime end start) :: Double)
      print runningTime
    _ -> putStrLn "USAGE: Main.exe SIZE"
