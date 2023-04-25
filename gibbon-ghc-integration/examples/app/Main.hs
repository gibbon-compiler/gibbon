module Main ( main ) where

import BinTree -- ( fast_print_double, fast_print_double2 )

import Data.Binary
import Data.ByteString.Lazy ( unpack )
import Data.Word

--------------------------------------------------------------------------------


data Exp = IntE Int
         | OpE Exp Exp
   deriving Show

instance Binary Exp where
      put (IntE i)      = do put (0 :: Word8)
                             put i

      put (OpE e1 e2) = do put (1 :: Word8)
                           put e1
                           put e2

      get = do t <- get :: Get Word8
               case t of
                    0 -> do i <- get
                            return (IntE i)
                    1 -> do e1 <- get
                            e2 <- get
                            return (OpE e1 e2)

--------------------------------------------------------------------------------

main :: IO ()
main = do
  let expr = OpE (IntE 10) (IntE 11)
  print (unpack (encode expr))
  let tr = Node 10 (Leaf 10 10) (Leaf 20 20) :: Tree Int
  print (unpack (encode tr))
  _ <- fast_print_double  3.0
  _ <- fast_print_double2 10.0
  pure ()
