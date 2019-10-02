module Helpers ( Sym, eqsym, quote ) where

type Sym = String

eqsym :: Sym -> Sym -> Bool
eqsym = (==)

quote = id
