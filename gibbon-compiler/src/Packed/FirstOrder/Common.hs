{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
-- {-# LANGUAGE DeriveAnyClass #-} -- Actually breaks Applicative SymM deriving!
-- {-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Utilities and common types.

module Packed.FirstOrder.Common
       (
         -- * Global constants or conventions
--         cPackedTagSize, cPointerTagSize -- FINISHME
         mkUnpackerName
       , mkPrinterName

         -- * Type and Data constructors
       , DataCon, TyCon, IsBoxed

         -- * Variables and gensyms
       , Var(..), fromVar, toVar, varAppend, SyM, gensym, genLetter, runSyM
       , cleanFunName, mkCopyFunName, isCopyFunName

         -- * Regions and locations
       , LocVar, Region(..), Modality(..), LRM(..), dummyLRM
       , Multiplicity(..), regionVar

         -- * Environment and helpers
       , Env2(Env2) -- TODO: hide constructor
       , FunEnv
       , vEnv, fEnv, extendVEnv, extendsVEnv, extendFEnv, emptyEnv2
       , lookupVEnv

         -- * Runtime configuration
       , RunConfig(..), getRunConfig

         -- * Top-level function defs
       , FunDef(..), FunDefs
       , insertFD, fromListFD

         -- * Data definitions
       , DDef(..), DDefs, fromListDD, emptyDD, insertDD
       , lookupDDef, lookupDataCon, getConOrdering, getTyOfDataCon, getTagOfDataCon
       , Tag

         -- * Redirections and indirections
       , redirectionSize, redirectionTag, redirectionAlt
       , toIndrDataCon, fromIndrDataCon, isIndrDataCon, indirectionTag, indirectionAlt

         -- * Misc helpers
       , (#), (!!!), fragileZip, fragileZip', sdoc, ndoc, abbrv, l

         -- * Debugging/logging:
       , dbgLvl, dbgPrint, dbgPrintLn, dbgTrace, dbgTraceIt, minChatLvl
--       , err
       , internalError

         -- * Establish conventions for the output of #lang gibbon:
       , truePrinted, falsePrinted
       ) where

import Control.DeepSeq (NFData(..), force)
import Control.Exception (evaluate)
import Control.Monad.State.Strict
import Data.Char
import Data.List as L
import Data.Map as M
import Data.String
import Data.Symbol
import Data.Loc
import Data.Word
import GHC.Generics
import Text.PrettyPrint.GenericPretty
import Text.PrettyPrint.HughesPJ as PP
import System.IO
import System.Environment
import System.IO.Unsafe (unsafePerformIO)
import Debug.Trace
import Language.C.Quote.CUDA (ToIdent, toIdent)


-- | Orphaned instance: read without source locations.
instance Read t => Read (L t) where
  readsPrec n str = [ (L NoLoc a,s) | (a,s) <- readsPrec n str ]

-- type CursorVar = Var
newtype Var = Var Symbol
  deriving (Eq, Ord, Read, Show)

instance Out Var where
  doc         = doc . fromVar
  docPrec n v = docPrec n (fromVar v)

instance NFData Var where
  rnf = (rnf . fromVar)

instance ToIdent Var where
  toIdent = (toIdent . fromVar)

instance IsString Var where
  fromString = toVar

fromVar :: Var -> String
fromVar (Var v) = unintern v

toVar :: String -> Var
toVar s = Var $ intern s

-- | String concatenation on variables.
varAppend :: Var -> Var -> Var
varAppend x y = toVar (fromVar x ++ fromVar y)

type DataCon = String
type TyCon   = String

-- | Abstract location variables.
type LocVar = Var
-- TODO: add start(r) form.


-- See https://github.com/iu-parfunc/gibbon/issues/79 for more details
-- | Region variants (multiplicities)
data Multiplicity
    = Bounded     -- ^ Contain a finite number of values and can be
                  --   stack-allocated.

    | Infinite    -- ^ Consist of a linked list of buffers, spread
                  --   throughout memory (though possible constrained
                  --   to 4GB regions). Writing into these regions requires
                  --   bounds-checking. The buffers can start very small
                  --   at the head of the list, but probably grow
                  --   geometrically in size, making the cost of traversing
                  --   all of them logarithmic.

    | BigInfinite -- ^ These regions are infinite, but also have the
                  --   expectation of containing many values. Thus we give
                  --   them large initial page sizes. This is also could be
                  --   the appropriate place to use mmap to grow the region
                  --   and to establish guard places.
  deriving (Read,Show,Eq,Ord,Generic)

instance Out Multiplicity where
  doc = text . show

instance NFData Multiplicity where
  rnf _ = ()

-- | An abstract region identifier.  This is used inside type signatures and elsewhere.
data Region = GlobR Var Multiplicity -- ^ A global region with lifetime equal to the
                                     --   whole program.
            | DynR Var Multiplicity  -- ^ A dynamic region that may be created or
                                     --   destroyed, tagged by an identifier.
            | VarR Var               -- ^ A region metavariable that can range over
                                     --   either global or dynamic regions.
  deriving (Read,Show,Eq,Ord, Generic)
instance Out Region
instance NFData Region where
  rnf (GlobR v _) = rnf v
  rnf (DynR v _)  = rnf v
  rnf (VarR v)    = rnf v

-- | The modality of locations and cursors: input/output, for reading
-- and writing, respectively.
data Modality = Input | Output
  deriving (Read,Show,Eq,Ord, Generic)
instance Out Modality
instance NFData Modality where
  rnf Input  = ()
  rnf Output = ()

-- | A location and region, together with modality.
data LRM = LRM { lrmLoc :: LocVar
               , lrmReg :: Region
               , lrmMode :: Modality }
  deriving (Read,Show,Eq,Ord, Generic)
instance Out LRM
instance NFData LRM where
  rnf (LRM a b c)  = rnf a `seq` rnf b `seq` rnf c

-- | A designated doesn't-really-exist-anywhere location.
dummyLRM :: LRM
dummyLRM = LRM "l_dummy" (VarR "r_dummy") Input

regionVar :: Region -> Var
regionVar r = case r of
                  GlobR v _ -> v
                  DynR  v _ -> v
                  VarR  v   -> v

--------------------------------------------------------------------------------
-- Helper methods to integrate the Data.Loc with Gibbon

l :: a -> L a
l x = L NoLoc x

deriving instance Generic Loc
deriving instance Generic Pos

instance Out Loc where
  docPrec _ loc = doc loc

  doc loc =
    case loc of
      Loc start _end -> doc start
      NoLoc -> PP.empty

instance Out Pos where
  docPrec _ pos = doc pos

  doc (Pos path line col _) = hcat [doc path, colon, doc line, colon, doc col]

--------------------------------------------------------------------------------

-- | A common currency for a two part environment consisting of
-- function bindings and regular value bindings.
data Env2 a = Env2 { vEnv :: M.Map Var a
                   , fEnv :: FunEnv a }


-- |
emptyEnv2 :: Env2 a
emptyEnv2 = Env2 { vEnv = M.empty
                 , fEnv = M.empty}

-- | Extend non-function value environment.
extendVEnv :: Var -> a -> Env2 a -> Env2 a
extendVEnv v t (Env2 ve fe) = Env2 (M.insert v t ve) fe

-- | Extend multiple times in one go.
extendsVEnv :: M.Map Var a -> Env2 a -> Env2 a
extendsVEnv mp (Env2 ve fe) = Env2 (M.union mp ve) fe

lookupVEnv :: Out a => Var -> Env2 a -> a
lookupVEnv v env2 = (vEnv env2) # v

-- | Extend function type environment.
extendFEnv :: Var -> (a,a) -> Env2 a -> Env2 a
extendFEnv v t (Env2 ve fe) = Env2 ve (M.insert v t fe)


--------------------------------------------------------------------------------

-- | Type environment for function defs only.  This works with type
-- representations that do not include arrow types.
type FunEnv a = M.Map Var (a, a)

-- Primitive for now:
type DDefs a = Map Var (DDef a)

type IsBoxed = Bool

-- | Data type definitions.
--
-- Monomorphism: In the extreme case we can strip packed datatypes of
-- all type parameters, or we can allow them to retain type params but
-- require that they always be fully instantiated to monomorphic types
-- in the context of our monomorphic programs.
--
-- Here we allow individual to be marked with whether or not they
-- should be boxed.  We say that a regular, pointer-based datatype has
-- all-boxed fields, whereas a fully serialized datatype has no boxed
-- fields.
data DDef a = DDef { tyName:: Var
                   -- , tyArgs:: [Var] -- ^ No polymorphism for now!
                   , dataCons :: [(DataCon,[(IsBoxed,a)])] }
  deriving (Read,Show,Eq,Ord, Functor, Generic)

instance NFData a => NFData (DDef a) where
  -- rnf DDef

instance Out a => Out (DDef a)
instance (Out k,Out v) => Out (Map k v) where
  doc         = doc . M.toList
  docPrec n v = docPrec n (M.toList v)

type Tag = Word8

-- DDef utilities:

-- | Lookup a ddef in its entirety
lookupDDef :: Out a => DDefs a -> Var -> DDef a
lookupDDef mp v =
    case M.lookup v mp of
      Just x -> x
      Nothing -> error $ "lookupDDef failed on symbol: "++ fromVar v ++"\nDDefs: "++sdoc mp


-- | Get the canonical ordering for data constructors, currently based
-- on ordering in the original source code.  Takes a TyCon as argument.
getConOrdering :: Out a => DDefs a -> TyCon -> [DataCon]
getConOrdering dd tycon = L.map fst dataCons
  where DDef{dataCons} = lookupDDef dd (toVar tycon)

-- | Lookup the name of the TyCon that goes with a given DataCon.
--   Must be unique!
getTyOfDataCon :: Out a => DDefs a -> DataCon -> TyCon
getTyOfDataCon dds con = (fromVar . fst) $ lkp dds con

-- | Look up the numeric tag for a dataCon
getTagOfDataCon :: Out a => DDefs a -> DataCon -> Word8
getTagOfDataCon dds dcon =
    if dcon == indirectionTag
    then indirectionAlt
    else fromIntegral ix
  where Just ix = L.elemIndex dcon $ getConOrdering dds (fromVar tycon)
        (tycon,_) = lkp dds dcon

-- | Lookup the arguments to a data contstructor.
lookupDataCon :: Out a => DDefs a -> DataCon -> [a]
lookupDataCon dds con =
    -- dbgTrace 5 ("lookupDataCon -- "++sdoc(dds,con)) $
    L.map snd $ snd $ snd $ lkp dds con

-- | Lookup a Datacon.  Return (TyCon, (DataCon, [flds]))
lkp :: Out a => DDefs a -> DataCon -> (Var, (DataCon, [(IsBoxed,a)]))
lkp dds con =
   -- Here we try to lookup in ALL datatypes, assuming unique datacons:
  case [ (tycon,variant)
       | (tycon, DDef{dataCons}) <- M.toList dds
       , variant <- L.filter ((==con). fst) dataCons ] of
    [] -> error$ "lookupDataCon: could not find constructor "++show con
          ++", in datatypes:\n  "++show(doc dds)
    [hit] -> hit
    _ -> error$ "lookupDataCon: found multiple occurences of constructor "++show con
          ++", in datatypes:\n  "++show(doc dds)



insertDD :: DDef a -> DDefs a -> DDefs a
insertDD d = M.insertWith err' (tyName d) d
  where
   err' = error $ "insertDD: data definition with duplicate name: "++show (tyName d)

emptyDD :: DDefs a
emptyDD  = M.empty

fromListDD :: [DDef a] -> DDefs a
fromListDD = L.foldr insertDD M.empty

redirectionSize :: Int
redirectionSize = 9

redirectionTag :: DataCon
redirectionTag = "REDIRECTION"

redirectionAlt :: Num a => a
redirectionAlt = 100

indirectionTag :: DataCon
indirectionTag = "INDIRECTION"

indirectionAlt :: Num a => a
indirectionAlt = 90

toIndrDataCon :: DataCon -> DataCon
toIndrDataCon dcon = dcon ++ "^"

fromIndrDataCon :: DataCon -> DataCon
fromIndrDataCon = init

isIndrDataCon :: DataCon -> Bool
isIndrDataCon = isSuffixOf "^"

-- Fundefs
----------------------------------------

-- | A set of top-level recursive function definitions
type FunDefs ty ex = Map Var (FunDef ty ex)

data FunDef ty ex = FunDef { funName  :: Var
                               -- ^ Return type
                           , funArg   :: (Var,ty)
                           , funRetTy :: ty
                           , funBody  :: ex }
  deriving (Read,Show,Eq,Ord, Generic, Functor, Traversable, Foldable)

-- deriving
instance (NFData t, NFData e) => NFData (FunDef t e) where

instance (Out a, Out b) => Out (FunDef a b)

insertFD :: FunDef t e -> FunDefs t e -> FunDefs t e
insertFD d = M.insertWith err' (funName d) d
  where
   err' = error $ "insertFD: function definition with duplicate name: "++show (funName d)

fromListFD :: [FunDef t e] -> FunDefs t e
fromListFD = L.foldr insertFD M.empty


-- Gensym monad:
----------------------------------------

newtype SyM a = SyM (State Int a)
 deriving (Functor, Applicative, Monad, MonadState Int)

-- | Generate a unique symbol by attaching a numeric suffix.
gensym :: Var -> SyM Var
gensym v = state (\n -> (cleanFunName v `varAppend` toVar (show n), n + 1))

-- | Generate alphabetic variables 'a','b',...
genLetter :: SyM Var
genLetter = do
    n <- get
    modify (+1)
    return $ toVar $ [chr (n + ord 'a')]

runSyM :: Int -> SyM a -> (a,Int)
runSyM n (SyM a) = runState a n

-- | Filter out non-C compatible characters.  This naively assumes it
-- will get no conflicts.  Which may be correct if function names were
-- gensym'd also....
cleanFunName :: Var -> Var
cleanFunName f =
  toVar [ if isNumber c || isAlpha c
          then c
          else '_'
        | c <- (fromVar f) ]

----------------------------------------

-- | An alias for the error function we want to use throughout this project.
{-# INLINE err #-}
err :: String -> a
err = error

-- | An error that is OUR FAULT, i.e. an internal bug in the compiler.
internalError :: String -> a
internalError s = error ("internal error: "++s)


(#) :: (Ord a, Out a, Out b, Show a)
    => Map a b -> a -> b
m # k = case M.lookup k m of
          Just x  -> x
          Nothing -> err $ "Map lookup failed on key: "++show k
                     ++ " in map:\n "++ show (doc m)


(!!!) :: (Out a) => [a] -> Int -> a
ls0 !!! ix0 = go ls0 ix0
 where
   go [] _ = err $ "Not enough elements in list to retrieve "++show ix0
                   ++", list:\n" ++ abbrv 300 ls0
   go (x:_) 0 = x
   go (_:xs) n = go xs (n-1)


fragileZip :: (Show a, Show b) => [a] -> [b] -> [(a, b)]
fragileZip [] [] = []
fragileZip (a:as) (b:bs) = (a,b) : fragileZip as bs
fragileZip as [] = err$ "fragileZip: right ran out, while left still has: "++show as
fragileZip [] bs = err$ "fragileZip: left ran out, while right still has: "++show bs


-- | Like fragileZip, but takes a custom error message.
fragileZip' :: (Show a, Show b) => [a] -> [b] -> String -> [(a, b)]
fragileZip' [] [] _ = []
fragileZip' (a:as) (b:bs) m = (a,b) : fragileZip' as bs m
fragileZip' _ [] m = error m
fragileZip' [] _ m = error m

-- | Handy combination of show and doc
sdoc :: Out a => a -> String
sdoc = show . doc

-- | Like sdoc but inserts newline if it is longish.
ndoc :: Out a => a -> String
ndoc x = let s = sdoc x in
         if L.length s > 40
         then "\n  " ++ s
         else s

-- | Like ndoc/sdoc but cut it off with "..." after a char limit.
abbrv :: (Out a) => Int -> a -> String
abbrv n x =
    let str = show (doc x)
        len = length str
    in if len <= n
       then str
       else L.take (n-3) str ++ "..."

----------------------------------------------------------------------------------------------------
-- Global parameters
----------------------------------------------------------------------------------------------------

-- | Runtime configuration for executing interpreters.
data RunConfig =
    RunConfig { rcSize  :: Int
              , rcIters :: Word64
              , rcDbg   :: Int
              , rcCursors :: Bool -- ^ Do we support cursors in L1.Exp at this point in the compiler.
              }

-- | We currently use the hacky approach of using env vars OR command
-- line args to set the two universal benchmark params: SIZE and ITERS.
--
-- This takes extra, optional command line args [Size, Iters] provided
-- after the file to process on the command line.  If these are not
-- present it
getRunConfig :: [String] -> IO RunConfig
getRunConfig ls =
 case ls of
   [] -> case L.lookup "SIZE" theEnv of
           Nothing -> getRunConfig ["1"]
           Just n  -> getRunConfig [n]
   [sz] -> case L.lookup "ITERS" theEnv  of
             Nothing -> getRunConfig [sz,"1"]
             Just i  -> getRunConfig [sz,i]
   [sz,iters] ->
     return $ RunConfig { rcSize=read sz, rcIters=read iters, rcDbg= dbgLvl, rcCursors= False }
   _ -> error $ "getRunConfig: too many command line args, expected <size> <iters> at most: "++show ls


----------------------------------------------------------------------------------------------------
-- DEBUGGING
----------------------------------------------------------------------------------------------------

theEnv :: [(String, String)]
theEnv = unsafePerformIO getEnvironment

-- | Debugging flag shared by all modules.
--   This is activated by setting the environment variable DEBUG=1..5
dbgLvl :: Int
dbgLvl = case L.lookup "DEBUG" theEnv of
       Nothing  -> defaultDbg
       Just ""  -> defaultDbg
       Just "0" -> defaultDbg
       Just s   ->
         case reads s of
           ((n,_):_) ->
               if n >= minChatLvl
               then trace (" ! Responding to env Var: DEBUG="++s) n
               else n
           [] -> error$"Attempt to parse DEBUG env var as Int failed: "++show s

-- | We should not create chatter below this level.  DEBUG=1 is used
-- for assertions only, not chatter.
minChatLvl :: Int
minChatLvl = 2

defaultDbg :: Int
defaultDbg = 0

-- | Print if the debug level is at or above a threshold.
dbgPrint :: Int -> String -> IO ()
dbgPrint lvl str = if dbgLvl < lvl then return () else do
    _ <- evaluate (force str) -- Force it first to squeeze out any dbgTrace msgs.
    hPutStrLn stderr str
    -- hPrintf stderr str
    -- hFlush stderr
    -- printf str
    -- hFlush stdout

-- | Conditional version of Debug.Trace.trace
dbgTrace :: Int -> String -> a -> a
dbgTrace lvl msg val =
    if   dbgLvl < lvl
    then val
    else trace msg val

dbgTraceIt :: Show a => Int -> String -> a -> a
dbgTraceIt lvl msg x = dbgTrace lvl (msg++": "++show x) x

dbgPrintLn :: Int -> String -> IO ()
dbgPrintLn lvl str = dbgPrint lvl (str++"\n")



-- | For now this is designed to match the Racket output of "#lang
-- gibbon" which itself should change once we implement a custom
-- printer.
truePrinted :: String
truePrinted = "#t"
-- truePrinted = "true"

falsePrinted :: String
falsePrinted = "#f"


-- | Map a DataCon onto the name of the generated unpack function.
mkUnpackerName :: TyCon -> Var
mkUnpackerName tyCons = toVar $ "unpack_" ++ tyCons

-- | Map a DataCon onto the name of the generated print function.
mkPrinterName :: DataCon -> Var
mkPrinterName tyCons = toVar $ "print_" ++ tyCons

mkCopyFunName :: DataCon -> Var
mkCopyFunName dcon = "copy_" `varAppend` (toVar dcon)

isCopyFunName :: Var -> Bool
isCopyFunName = isPrefixOf "copy_" . fromVar
