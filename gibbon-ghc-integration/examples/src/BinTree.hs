{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE TemplateHaskell          #-}
{-# LANGUAGE DeriveGeneric          #-}

module BinTree where

-- import Gibbon.Plugin0 ( PackedAnn(..) )
import Gibbon.Plugin ( liftPacked, Packed, PackedAnn(..) )
import Foreign
import Foreign.C.Types
import GHC.Generics
import Data.Binary

import qualified Language.C.Inline as C

--------------------------------------------------------------------------------

data Tree = Leaf Int
          | Node Int Tree Tree
  deriving (Generic)

instance Binary Tree

-- {-# ANN mkTree_seq LiftPacked #-}
mkTree_seq :: Int -> Tree
mkTree_seq i =
  if i <= 0
  then Leaf 1
  else
      let x = mkTree_seq (i-1)
          y = mkTree_seq (i-1)
      in Node i x y

-- {-# ANN sumTree_seq LiftPacked #-}
sumTree_seq :: Tree -> Int
sumTree_seq tr =
  case tr of
    Leaf i     -> i
    Node _ a b ->
      let x = sumTree_seq a
          y = sumTree_seq b
      in x + y

bench1 :: Int -> Int
bench1 n = sumTree_seq (mkTree_seq n)

{-# ANN liftbench1 LiftPacked #-}
liftbench1 :: Int -> Int
liftbench1 n = sumTree_seq (mkTree_seq n)


foreign import ccall unsafe "c_liftbench1"
  cfastbench1 :: CInt -> IO CInt

fastbench1 :: Int -> IO Int
fastbench1 x = do
  y <- cfastbench1 (fromIntegral x)
  pure $ fromIntegral y

--------------------------------------------------------------------------------

-- foreign import ccall "print_double"
--   c_print_double :: CDouble -> IO CInt

-- fast_print_double :: Double -> IO Int
-- fast_print_double x = do
--   y <- c_print_double (realToFrac x)
--   pure $ fromIntegral y

--------------------------------------------------------------------------------


{-

C.include "<stdlib.h>"
C.include "<stdio.h>"
C.include "<stdint.h>"

C.verbatim "int print_double2(double i) { printf(\"Printing a double in C (2): %lf \", i); return 0;}"

foreign import ccall "print_double2"
  c_print_double2 :: CDouble -> IO CInt

fast_print_double2 :: Double -> IO Int
fast_print_double2 x = do
   y <- c_print_double2 (realToFrac x)
   pure $ fromIntegral y

-}
