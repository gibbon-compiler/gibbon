{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE TemplateHaskell          #-}

module BinTree where

import Gibbon.Plugin ( PackedAnn(..) )
import Foreign
import Foreign.C.Types

import qualified Language.C.Inline as C

--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

foreign import ccall "print_double"
  c_print_double :: CDouble -> IO CInt

fast_print_double :: Double -> IO Int
fast_print_double x = do
  y <- c_print_double (realToFrac x)
  pure $ fromIntegral y

--------------------------------------------------------------------------------

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
