{-# LANGUAGE CPP            #-}
{-# LANGUAGE BangPatterns   #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric  #-}

module Main where

import Prelude hiding (iterate)
import Control.Exception
import Data.IORef
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

type SymHash = M.Map Sym Sym
type IntHash = M.Map Sym Int

empty_hash = M.empty
lookup_hash env k = M.findWithDefault k k env
insert_hash env k v = M.insert k v env
contains_hash env k = M.member k env

empty_int_hash = M.empty
lookup_int_hash env k = M.findWithDefault k k env
insert_int_hash env k v = M.insert k v env
contains_int_hash env k = M.member k env

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

global_gensym_counter :: IORef Int
global_gensym_counter = unsafePerformIO (newIORef 0)

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
      let n = read size
      let ex = (make_big_ex n 0)
      let !prg = force $ (ProgramA intTy ex)
      start <- getCurrentTime
      !compiled <- pure $ force $ compile2 prg
      end <- getCurrentTime
      let runningTime = ((fromRational $ toRational $ diffUTCTime end start) :: Double)
      print runningTime
    _ -> print "./Main.exe SIZE"
