module Helpers ( Sym, eqsym, quote, printsym, printint ) where
import System.IO.Unsafe
    
type Sym = String

eqsym :: Sym -> Sym -> Bool
eqsym = (==)

quote = id

printsym :: Sym -> Int
printsym s = let _ = unsafePerformIO (print s) in 0

printint :: Int -> Int
printint i = let _ = unsafePerformIO (print i) in 0
