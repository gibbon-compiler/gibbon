module Gibbon.Passes.LLVM.Utils where

import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Short as S


-- |
toByteString :: String -> S.ShortByteString
toByteString = S.toShort . B.pack


data InstrRet = NamedVar S.ShortByteString | FreshVar | Void
  deriving (Eq, Ord, Show, Read)
