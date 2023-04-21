module Main ( main ) where

import BinTree ( fast_print_double, fast_print_double2 )

--------------------------------------------------------------------------------

main :: IO ()
main = do
  _ <- fast_print_double  3.0
  _ <- fast_print_double2 10.0
  pure ()
