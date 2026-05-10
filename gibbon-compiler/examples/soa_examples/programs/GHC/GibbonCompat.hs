{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fno-full-laziness -fno-cse #-}
module GibbonCompat
  ( printsym
  , quote
  , iterate
  , printsymIO
  , iterateIO
  , sizeParam
  , GibbonShow(..)
  , runGibbonMain
  , runGibbonMainIO
  ) where

import Prelude hiding (iterate)
import System.Environment (getArgs)
import System.CPUTime (getCPUTime)
import System.IO (hFlush, stdout)
import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Control.Exception (evaluate)
import Control.DeepSeq (NFData, deepseq)
import Text.Printf (printf)
import Data.List (intercalate)

itersRef :: IORef Int
itersRef = unsafePerformIO (newIORef 1)
{-# NOINLINE itersRef #-}

sizeParamRef :: IORef Int
sizeParamRef = unsafePerformIO (newIORef 0)
{-# NOINLINE sizeParamRef #-}

sizeParam :: Int
sizeParam = unsafePerformIO (readIORef sizeParamRef)
{-# NOINLINE sizeParam #-}

quote :: String -> String
quote = id

printsym :: String -> ()
printsym s = unsafePerformIO $ do
  if s == "NEWLINE"
    then putStrLn ""
    else putStr s
  hFlush stdout
  return ()
{-# NOINLINE printsym #-}

printsymIO :: String -> IO ()
printsymIO s =
  if s == "NEWLINE"
    then putStrLn "" >> hFlush stdout
    else putStr s >> hFlush stdout

printIterTimes :: [Double] -> IO ()
printIterTimes times = do
  putStr "ITER TIMES: ["
  case times of
    [] -> putStrLn "]"
    _  -> do
      let initTimes = init times
      mapM_ (\t -> printf "%.6f, " t) initTimes
      printf "%.6f]\n" (last times)
  hFlush stdout

-- Gibbon's iterate repeats the computation and prints ITER TIMES.
-- Here we approximate by forcing the expression each iteration.
iterate :: a -> a
iterate x = unsafePerformIO $ do
  iters <- readIORef itersRef
  times <- loop iters []
  printIterTimes (reverse times)
  return x
  where
    loop 0 acc = return acc
    loop n acc = do
      t0 <- getCPUTime
      _ <- evaluate x
      t1 <- getCPUTime
      let t = fromIntegral (t1 - t0) / 1.0e12
      loop (n - 1) (t : acc)
{-# NOINLINE iterate #-}

iterateIO :: NFData a => (() -> a) -> IO a
iterateIO thunk = do
  iters <- readIORef itersRef
  times <- loop iters []
  printIterTimes (reverse times)
  let v = thunk ()
  v `deepseq` return v
  where
    loop 0 acc = return acc
    loop n acc = do
      t0 <- getCPUTime
      v <- evaluate (thunk ())
      v `deepseq` return ()
      t1 <- getCPUTime
      let t = fromIntegral (t1 - t0) / 1.0e12
      loop (n - 1) (t : acc)

runGibbonMain :: a -> IO ()
runGibbonMain gmain = do
  args <- getArgs
  let iters = case args of
                ["--iterate", n] -> case reads n of
                                      [(v, "")] -> v
                                      _ -> 1
                _ -> 1
      sz = case args of
             ["--size-param", n] -> case reads n of
                                       [(v, "")] -> v
                                       _ -> 0
             ["--salt", n] -> case reads n of
                                 [(v, "")] -> v
                                 _ -> 0
             _ -> 0
  writeIORef itersRef iters
  writeIORef sizeParamRef sz
  _ <- evaluate gmain
  return ()

runGibbonMainIO :: GibbonShow a => IO a -> IO ()
runGibbonMainIO action = do
  args <- getArgs
  let iters = case args of
                ["--iterate", n] -> case reads n of
                                      [(v, "")] -> v
                                      _ -> 1
                _ -> 1
      sz = case args of
             ["--size-param", n] -> case reads n of
                                       [(v, "")] -> v
                                       _ -> 0
             ["--salt", n] -> case reads n of
                                 [(v, "")] -> v
                                 _ -> 0
             _ -> 0
  writeIORef itersRef iters
  writeIORef sizeParamRef sz
  res <- action
  putStrLn (gibbonShowTop res)
  hFlush stdout
  return ()

class GibbonShow a where
  gibbonShow :: a -> String
  gibbonShowTop :: a -> String
  gibbonShowTop = gibbonShow

instance GibbonShow Int where
  gibbonShow = show

instance GibbonShow Bool where
  gibbonShow b = if b then "#t" else "#f"

instance (GibbonShow a, GibbonShow b) => GibbonShow (a, b) where
  gibbonShow (a, b) = "#(" ++ intercalate " " [gibbonShow a, gibbonShow b] ++ ")"
  gibbonShowTop x = "'" ++ gibbonShow x

instance (GibbonShow a, GibbonShow b, GibbonShow c) => GibbonShow (a, b, c) where
  gibbonShow (a, b, c) = "#(" ++ intercalate " " [gibbonShow a, gibbonShow b, gibbonShow c] ++ ")"
  gibbonShowTop x = "'" ++ gibbonShow x

instance (GibbonShow a, GibbonShow b, GibbonShow c, GibbonShow d) => GibbonShow (a, b, c, d) where
  gibbonShow (a, b, c, d) = "#(" ++ intercalate " " [gibbonShow a, gibbonShow b, gibbonShow c, gibbonShow d] ++ ")"
  gibbonShowTop x = "'" ++ gibbonShow x

instance (GibbonShow a, GibbonShow b, GibbonShow c, GibbonShow d, GibbonShow e)
      => GibbonShow (a, b, c, d, e) where
  gibbonShow (a, b, c, d, e) = "#(" ++ intercalate " " [gibbonShow a, gibbonShow b, gibbonShow c, gibbonShow d, gibbonShow e] ++ ")"
  gibbonShowTop x = "'" ++ gibbonShow x

instance (GibbonShow a, GibbonShow b, GibbonShow c, GibbonShow d, GibbonShow e, GibbonShow f)
      => GibbonShow (a, b, c, d, e, f) where
  gibbonShow (a, b, c, d, e, f) = "#(" ++ intercalate " " [gibbonShow a, gibbonShow b, gibbonShow c, gibbonShow d, gibbonShow e, gibbonShow f] ++ ")"
  gibbonShowTop x = "'" ++ gibbonShow x

instance (GibbonShow a, GibbonShow b, GibbonShow c, GibbonShow d, GibbonShow e, GibbonShow f, GibbonShow g)
      => GibbonShow (a, b, c, d, e, f, g) where
  gibbonShow (a, b, c, d, e, f, g) = "#(" ++ intercalate " " [gibbonShow a, gibbonShow b, gibbonShow c, gibbonShow d, gibbonShow e, gibbonShow f, gibbonShow g] ++ ")"
  gibbonShowTop x = "'" ++ gibbonShow x

instance (GibbonShow a, GibbonShow b, GibbonShow c, GibbonShow d, GibbonShow e, GibbonShow f, GibbonShow g, GibbonShow h)
      => GibbonShow (a, b, c, d, e, f, g, h) where
  gibbonShow (a, b, c, d, e, f, g, h) = "#(" ++ intercalate " " [gibbonShow a, gibbonShow b, gibbonShow c, gibbonShow d, gibbonShow e, gibbonShow f, gibbonShow g, gibbonShow h] ++ ")"
  gibbonShowTop x = "'" ++ gibbonShow x

instance (GibbonShow a, GibbonShow b, GibbonShow c, GibbonShow d, GibbonShow e, GibbonShow f, GibbonShow g, GibbonShow h, GibbonShow i)
      => GibbonShow (a, b, c, d, e, f, g, h, i) where
  gibbonShow (a, b, c, d, e, f, g, h, i) = "#(" ++ intercalate " " [gibbonShow a, gibbonShow b, gibbonShow c, gibbonShow d, gibbonShow e, gibbonShow f, gibbonShow g, gibbonShow h, gibbonShow i] ++ ")"
  gibbonShowTop x = "'" ++ gibbonShow x

instance (GibbonShow a, GibbonShow b, GibbonShow c, GibbonShow d, GibbonShow e, GibbonShow f, GibbonShow g, GibbonShow h, GibbonShow i, GibbonShow j)
      => GibbonShow (a, b, c, d, e, f, g, h, i, j) where
  gibbonShow (a, b, c, d, e, f, g, h, i, j) = "#(" ++ intercalate " " [gibbonShow a, gibbonShow b, gibbonShow c, gibbonShow d, gibbonShow e, gibbonShow f, gibbonShow g, gibbonShow h, gibbonShow i, gibbonShow j] ++ ")"
  gibbonShowTop x = "'" ++ gibbonShow x

instance (GibbonShow a, GibbonShow b, GibbonShow c, GibbonShow d, GibbonShow e, GibbonShow f, GibbonShow g, GibbonShow h, GibbonShow i, GibbonShow j, GibbonShow k)
      => GibbonShow (a, b, c, d, e, f, g, h, i, j, k) where
  gibbonShow (a, b, c, d, e, f, g, h, i, j, k) = "#(" ++ intercalate " " [gibbonShow a, gibbonShow b, gibbonShow c, gibbonShow d, gibbonShow e, gibbonShow f, gibbonShow g, gibbonShow h, gibbonShow i, gibbonShow j, gibbonShow k] ++ ")"
  gibbonShowTop x = "'" ++ gibbonShow x

instance (GibbonShow a, GibbonShow b, GibbonShow c, GibbonShow d, GibbonShow e, GibbonShow f, GibbonShow g, GibbonShow h, GibbonShow i, GibbonShow j, GibbonShow k, GibbonShow l)
      => GibbonShow (a, b, c, d, e, f, g, h, i, j, k, l) where
  gibbonShow (a, b, c, d, e, f, g, h, i, j, k, l) = "#(" ++ intercalate " " [gibbonShow a, gibbonShow b, gibbonShow c, gibbonShow d, gibbonShow e, gibbonShow f, gibbonShow g, gibbonShow h, gibbonShow i, gibbonShow j, gibbonShow k, gibbonShow l] ++ ")"
  gibbonShowTop x = "'" ++ gibbonShow x
