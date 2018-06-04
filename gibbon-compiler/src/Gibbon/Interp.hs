{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      : Gibbon.Interp
-- Description : Things related to interpreting Gibbon programs.
-----------------------------------------------------------------------------

module Gibbon.Interp
  ( Store(..), insertIntoStore, lookupInStore
  , Buffer(..), emptyBuffer
  , SerializedVal(..), Value(..), Log, ValEnv
  ) where

import Control.Monad.State
import Control.DeepSeq
import Data.ByteString.Builder (Builder)
import Data.Foldable as F
import Data.List as L
import Data.Map as M
import Data.Sequence as Seq (Seq, empty)
import Data.Word (Word8)
import Text.PrettyPrint.GenericPretty

import Gibbon.Common


-- Stores and buffers:
------------------------------------------------------------

-- | A store is an address space full of buffers.
data Store = Store (M.Map Var Buffer)
  deriving (Read,Eq,Ord,Generic, Show)

instance Out Store

insertIntoStore :: MonadState Store m => Var -> Buffer -> m ()
insertIntoStore v buf = modify (\(Store x) -> Store (M.insert v buf x))

lookupInStore :: MonadState Store m => Var -> m (Maybe Buffer)
lookupInStore v = do
  Store store <- get
  return (M.lookup v store)

data Buffer = Buffer (Seq SerializedVal)
  deriving (Read,Eq,Ord,Generic, Show)

instance Out Buffer

emptyBuffer :: Buffer
emptyBuffer = Buffer Seq.empty

data SerializedVal = SerTag Word8 DataCon | SerInt Int
  deriving (Read,Eq,Ord,Generic, Show)

byteSize :: SerializedVal -> Int
byteSize (SerInt _) = 8 -- FIXME: get this constant from elsewhere.
byteSize (SerTag _ _) = 1

instance Out SerializedVal
instance NFData SerializedVal

instance Out Word8 where
  doc w       = doc       (fromIntegral w :: Int)
  docPrec n w = docPrec n (fromIntegral w :: Int)

instance Out a => Out (Seq a) where
  doc s       = doc       (F.toList s)
  docPrec n s = docPrec n (F.toList s)

-- Values
-------------------------------------------------------------

-- | It's a first order language with simple values.
data Value = VInt Int
           | VBool Bool
           | VDict (M.Map Value Value)
-- FINISH:       | VList
           | VProd [Value]
           | VPacked DataCon [Value]

           | VCursor { bufID :: Int, offset :: Int }
             -- ^ Cursor are a pointer into the Store plus an offset into the Buffer.

  deriving (Read,Eq,Ord,Generic)

instance Out Value
instance NFData Value

instance Show Value where
 show v =
  case v of
   VInt n   -> show n
   VBool b  -> if b then truePrinted else falsePrinted
-- TODO: eventually want Haskell style tuple-printing:
--    VProd ls -> "("++ concat(intersperse ", " (L.map show ls)) ++")"
-- For now match Gibbon's Racket backend
   VProd ls -> "'#("++ concat(intersperse " " (L.map show ls)) ++")"
   VDict m      -> show (M.toList m)

   -- F(x) style.  Maybe we'll switch to sweet-exps to keep everything in sync:
   -- VPacked k ls -> k ++ show (VProd ls)

   -- For now, Racket style:
   VPacked k ls -> "(" ++ k ++ concat (L.map ((" "++) . show) ls) ++ ")"

   VCursor idx off -> "<cursor "++show idx++", "++show off++">"

type Log = Builder
type ValEnv = M.Map Var Value
