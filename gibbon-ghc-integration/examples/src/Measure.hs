{-# LANGUAGE BangPatterns #-}

module Measure where

import Control.Exception (evaluate)
-- import Control.Monad.Par hiding (runParIO)
-- import Control.Monad.Par.IO
import Control.DeepSeq
import Data.Int
import Data.List
import System.Mem (performMajorGC)
import Data.Time.Clock (getCurrentTime, diffUTCTime)

--------------------------------------------------------------------------------

median :: [Double] -> Double
median ls = (sort ls) !! (length ls `div` 2)

--------------------------------------------------------------------------------


-- benchPar :: (NFData a, NFData b) =>
--             (a -> Int64 -> Par b) -> a -> Int64 -> Int64 -> IO (b, Double, Double)
-- benchPar f arg iters cutoff = do
--     let !arg2 = force arg
--     tups <- mapM (\_ -> dotrialPar f arg2 cutoff) [1..iters]
--     let (results, times) = unzip tups
--     -- print times
--     let  selftimed = median times
--          batchtime = sum times
--     return $! (last results, selftimed, batchtime)

-- benchParIO :: (NFData a, NFData b) =>
--               (a -> Int64 -> ParIO b) -> a -> Int64 -> Int64 -> IO (b, Double, Double)
-- benchParIO f arg iters cutoff = do
--     let !arg2 = force arg
--     tups <- mapM (\_ -> dotrialParIO f arg2 cutoff) [1..iters]
--     let (results, times) = unzip tups
--     -- print times
--     let  selftimed = median times
--          batchtime = sum times
--     return $! (last results, selftimed, batchtime)

benchIO :: (NFData a, NFData b) =>
              (a -> IO b) -> a -> Int64 -> IO (b, Double, Double)
benchIO f arg iters = do
    let !arg2 = force arg
    tups <- mapM (\_ -> dotrialIO f arg2) [1..iters]
    let (results, times) = unzip tups
    -- print times
    let  selftimed = median times
         batchtime = sum times
    return $! (last results, selftimed, batchtime)


-- dotrialPar :: (NFData a, NFData b) =>
--               (a -> Int64 -> Par b) -> a -> Int64 -> IO (b, Double)
-- dotrialPar f arg cutoff = do
--     performMajorGC
--     t1 <- getCurrentTime
--     !a <- evaluate$ runPar $ (f arg cutoff)
--     t2 <- getCurrentTime
--     let delt = fromRational (toRational (diffUTCTime t2 t1))
--     putStrLn ("iter time: " ++ show delt)
--     return $! (a,delt)

-- dotrialParIO :: (NFData a, NFData b) =>
--                 (a -> Int64 -> ParIO b) -> a -> Int64 -> IO (b, Double)
-- dotrialParIO f arg cutoff = do
--     performMajorGC
--     t1 <- getCurrentTime
--     !a <- runParIO $ (f arg cutoff)
--     t2 <- getCurrentTime
--     let delt = fromRational (toRational (diffUTCTime t2 t1))
--     putStrLn ("iter time: " ++ show delt)
--     return $! (a,delt)

dotrialIO :: (NFData a, NFData b) =>
                (a -> IO b) -> a -> IO (b, Double)
dotrialIO f arg = do
    performMajorGC
    t1 <- getCurrentTime
    !a <- (f arg)
    t2 <- getCurrentTime
    let delt = fromRational (toRational (diffUTCTime t2 t1))
    putStrLn ("iter time: " ++ show delt)
    return $! (a,delt)

--------------------------------------------------------------------------------

bench :: (NFData a, Show b, NFData b) => (a -> b) -> a -> Int64 -> IO (b, Double, Double)
bench f arg iters = do
    let !arg2 = force arg
    !tups <- mapM (\_ -> dotrial f arg2) [1..iters]
    let (results, times) = unzip tups
    let selftimed = median times
        batchtime = sum times
    return $! (last results, selftimed, batchtime)

dotrial :: (NFData a, Show b, NFData b) => (a -> b) -> a -> IO (b, Double)
dotrial f arg = do
    performMajorGC
    t1 <- getCurrentTime
    !a <- evaluate $ (f arg)
    t2 <- getCurrentTime
    let delt = fromRational (toRational (diffUTCTime t2 t1))
    putStrLn ("iter time: " ++ show delt)
    return $! (a,delt)
