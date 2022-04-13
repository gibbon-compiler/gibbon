-- import Text.Printf
-- import System.CPUTime
-- import Data.IORef
-- import Data.Array.IO
-- import System.Time	( ClockTime(..) )
-- import Control.Monad 	( replicateM_ )
-- import System.IO
-- import System.Environment

-- class DeepSeq a where
-- deepSeq :: a -> b -> b
-- deepSeq = seq

-- instance DeepSeq Int

-- instance DeepSeq Tree where
-- deepSeq Empty b = b
-- deepSeq Node{left=l, right=r, i=i} b =
-- deepSeq l $ deepSeq r $ deepSeq i b

-- treeSize i = 2^(i+1) - 1

-- numIters max i = 2 * treeSize max `quot` treeSize i

-- data Tree = Node { left, right :: Tree,  i :: Int } | Empty

-- makeTree 0      = Node { left = Empty, right = Empty, i = 0 }
-- makeTree iDepth = Node { left  = makeTree (iDepth-1),
--             right = makeTree (iDepth-1),
--             i = 0 }

-- data MutTree = MutNode (IORef MutTree) (IORef MutTree) Int | MutEmpty

-- newMutNode x = do
-- l <- newIORef MutEmpty
-- r <- newIORef MutEmpty
-- return (MutNode l r x)

-- -- Build tree top down, assigning to older objects.
-- populate 0 node = return ()
-- populate iDepth (MutNode lref rref i) = do
-- l <- newMutNode iDepth
-- writeIORef lref l
-- r <- newMutNode iDepth
-- writeIORef rref r
-- populate (iDepth-1) l
-- populate (iDepth-1) r

-- ldepth MutEmpty = return 0
-- ldepth (MutNode l _ _) = do t <- readIORef l; ldepth t

-- timeConstruction max depth = do
--     let iNumIters = numIters max depth
--     --  printf "Creating %d trees of depth %d\n" iNumIters depth
--     tStart <- getCPUTime
--     replicateM_ iNumIters $ do
--     n <- newMutNode depth; populate depth n; touch n
--     tFinish <- getCPUTime
--     --  printf "\tTop down construction took "
--     --  ptimediff stdout tStart tFinish
--     --  printf "\n"
--     tStart <- getCPUTime
--     replicateM_ iNumIters $ do
--     let tempTree = makeTree depth
--     deepSeq tempTree (return ())
--     touch tempTree
--     tFinish <- getCPUTime
--     --  printf "\tBottom-up construction took "
--     --  ptimediff stdout tStart tFinish
--     --  printf "\n"
--     return ()

-- main = do
--     args <- getArgs
--     let
--     [kLongLivedTreeDepth,
--         kArraySize,
--         kMinTreeDepth,
--         kMaxTreeDepth] = map read args :: [Int]

--     hSetBuffering stdout NoBuffering
--     --  printf "Garbage Collector Test\n"
--     tStart <- getCPUTime

--     -- Create a long lived object or two
--     --  printf " Creating a long-lived binary tree of depth %d\n" kLongLivedTreeDepth
--     let longLivedTree1 = makeTree kLongLivedTreeDepth
--     deepSeq longLivedTree1 (return ())

--     --  printf " Creating a long-lived mutable tree of depth %d\n" kLongLivedTreeDepth
--     longLivedTree2 <- newMutNode kLongLivedTreeDepth;
--     populate kLongLivedTreeDepth longLivedTree2

--     -- Create long-lived array, filling half of it
--     --  printf " Creating a long-lived array of %d doubles\n" kArraySize
--     array <- newArray (1,kArraySize) 0.0
--     let _ = array :: IOArray Int Double
--     sequence_ [ writeArray array i (1.0 / fromIntegral i)
--         | i <- [ 1 .. kArraySize `quot` 2 ] ]

--     sequence_ [ timeConstruction kMaxTreeDepth d
--             | d <- [ kMinTreeDepth, kMinTreeDepth+2 .. kMaxTreeDepth ] ]

--     touch longLivedTree1
--     ldepth longLivedTree2
--     touch array

-- -- Utils

-- ptimediff :: Handle -> Integer -> Integer -> IO ()
-- ptimediff hout t0 t1 =
--     hPrintf hout "%d.%02d" secs (psecs `quot` 10^10)
--     where  (secs,psecs) = (t1 - t0) `quotRem` (10^12)

-- touch :: a -> IO ()
-- touch a = a `seq` return ()

-- TODO write, fix and test