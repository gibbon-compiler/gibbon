{-# LANGUAGE FlexibleContexts #-}

-- |
-- Module      : Gibbon.Interp
-- Description : Things related to interpreting Gibbon programs.
-----------------------------------------------------------------------------

module Gibbon.Interp
  ( Interp(..)

  , Store(..), insertIntoStore, lookupInStore
  , Buffer(..), emptyBuffer, insertAtBuffer
  , SerializedVal(..), Value(..), Log, ValEnv

  , execAndPrint, deserialize, strToInt, lookup3
  ) where

import Control.Monad.State
import Control.DeepSeq
import Data.ByteString.Builder (Builder)
import Data.Char (ord)
import Data.Foldable as F
import Data.List as L
import Data.Map as M
import Data.Sequence (Seq, ViewL(..))
import Data.Word (Word8)
import System.IO.Unsafe (unsafePerformIO)
import Text.PrettyPrint.GenericPretty
import qualified Data.ByteString.Lazy.Char8 as B
import qualified Data.Sequence as S

import Gibbon.L1.Syntax
import Gibbon.Common

--------------------------------------------------------------------------------
-- Things which can be interpreted to yield a final, printed value.
--------------------------------------------------------------------------------

-- | Pure Gibbon programs, at any stage of compilation, should always
-- be evaluatable to a unique value.  The only side effects are timing.
class Interp a where
  {-# MINIMAL interpProg #-}

  interpProg :: RunConfig -> a -> IO (Value, B.ByteString)

  -- | Interpret while ignoring timing constructs, and dropping the
  -- corresponding output to stdout.
  interpNoLogs :: RunConfig -> a -> String
  interpNoLogs rc p = unsafePerformIO $ show . fst <$> interpProg rc p

  -- | Interpret and produce a "log" of output lines, as well as a
  -- final, printed result.  The output lines include timing information.
  interpWithStdout :: RunConfig -> a -> IO (String,[String])
  interpWithStdout rc p = do
   (v,logs) <- interpProg rc p
   return (show v, lines (B.unpack logs))


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
  return $ M.lookup v store

data Buffer = Buffer (Seq SerializedVal)
  deriving (Read,Eq,Ord,Generic, Show)

instance Out Buffer

emptyBuffer :: Buffer
emptyBuffer = Buffer S.empty

-- | Insert a value at a particular index in the buffer
insertAtBuffer :: Int -> SerializedVal -> Buffer -> Buffer
insertAtBuffer i v (Buffer b) = Buffer (S.insertAt i v b)

data SerializedVal = SerTag Word8 DataCon | SerInt Int | SerBool Int
  deriving (Read,Eq,Ord,Generic, Show)

byteSize :: SerializedVal -> Int
byteSize (SerInt _) = 8 -- FIXME: get this constant from elsewhere.
byteSize (SerBool _) = 8
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
           | VProd [Value]
           | VPacked DataCon [Value]
           | VLoc { bufID :: Var, offset :: Int }
           | VCursor { bufID :: Var, offset :: Int }
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

   VLoc buf off -> "<location "++show buf++", "++show off++">"

   VCursor idx off -> "<cursor "++show idx++", "++show off++">"

type Log = Builder
type ValEnv = M.Map Var Value

--------------------------------------------------------------------------------

-- | Code to read a final answer back out.
deserialize :: (Out ty) => DDefs ty -> Seq SerializedVal -> Value
deserialize ddefs seq0 = final
 where
  ([final],_) = readN 1 seq0

  readN 0 seq1 = ([],seq1)
  readN n seq1 =
     case S.viewl seq1 of
       S.EmptyL -> error $ "deserialize: unexpected end of sequence: "++ndoc seq0
       SerInt i :< rst ->
         let (more,rst') = readN (n-1) rst
         in (VInt i : more, rst')

       SerBool i :< rst ->
         let (more,rst') = readN (n-1) rst
             -- 1 is True
             b = i /= 0
         in (VBool b : more, rst')

       SerTag _ k :< rst ->
         let (args,rst')  = readN (length (lookupDataCon ddefs k)) rst
             (more,rst'') = readN (n-1) rst'
         in (VPacked k args : more, rst'')


execAndPrint :: (Interp (Prog ex)) => RunConfig -> Prog ex -> IO ()
execAndPrint rc prg = do
  (val,logs) <- interpProg rc prg
  B.putStr logs
  case val of
    -- Special case: don't print void return:
    VProd [] -> return () -- FIXME: remove this.
    _ -> print val

strToInt :: String -> Int
strToInt = product . L.map ord

lookup3 :: (Eq k, Show k, Show a, Show b) => k -> [(k,a,b)] -> (k,a,b)
lookup3 k ls = go ls
  where
   go [] = error$ "lookup3: key "++show k++" not found in list:\n  "++L.take 80 (show ls)
   go ((k1,a1,b1):r)
      | k1 == k   = (k1,a1,b1)
      | otherwise = go r
