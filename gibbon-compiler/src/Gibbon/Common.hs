{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE CPP #-}

-- | Utilities and common types.
module Gibbon.Common
       (
         -- * Variables
         Var(..), LocVar, RegVar, fromVar, toVar, varAppend, toEndV, toSeqV, cleanFunName
       , TyVar(..), isUserTv

         -- * Gensym monad
       , SyM, gensym, gensym_tag, genLetter, newUniq, runSyM

         -- * PassM monad
       , PassM, runPassM, defaultRunPassM, defaultPackedRunPassM
       , getDynFlags

         -- * Gibbon configuration
       , Config(..), Input(..), Mode(..), Backend(..), defaultConfig
       , RunConfig(..), getRunConfig, defaultRunConfig, getGibbonConfig

         -- * Misc helpers
       , SSModality(..), (#), (!!!), fragileZip, fragileZip', sdoc, ndoc, abbrv
       , lookup3, fst3, snd3, thd3, cataM

         -- * Debugging/logging:
       , dbgLvl, dbgPrint, dbgPrintLn, dbgTrace, dbgTraceIt, minChatLvl
       , internalError, dumpIfSet

         -- * Establish conventions for the output of #lang gibbon:
       , truePrinted, falsePrinted
       )
where

import Control.DeepSeq (NFData(..), force)
import Control.Exception (evaluate)
#if !MIN_VERSION_base(4,15,0)
import Control.Monad.Fail
#endif
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.Functor.Foldable
import Data.Char
import qualified Data.List as L
import Data.Map as M
import Data.String
import Data.Symbol
import Data.Word
import GHC.Generics
import GHC.Stack (HasCallStack)
import Text.PrettyPrint.GenericPretty
import Text.PrettyPrint as PP hiding (Mode(..), Style(..))
import System.IO
import System.Environment
import System.FilePath  ( replaceExtension )
import System.IO.Unsafe ( unsafePerformIO )
import System.Random    ( randomIO )
import Debug.Trace
import Language.C.Quote.CUDA (ToIdent, toIdent)

import Gibbon.DynFlags

--------------------------------------------------------------------------------

-- type CursorVar = Var
newtype Var = Var Symbol
  deriving (Eq, Ord, Read, Show)

instance Out Var where
  doc         = text . fromVar
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

-- | Filter out non-C compatible characters.  This naively assumes it
-- will get no conflicts.  Which may be correct if function names were
-- gensym'd also....
cleanFunName :: Var -> Var
cleanFunName f =
  toVar [ if isNumber c || isAlpha c
          then c
          else '_'
        | c <- (fromVar f) ]
toEndV :: Var -> Var
toEndV = varAppend "end_"

toSeqV :: Var -> Var
toSeqV v = varAppend v (toVar "_seq")

-- | Abstract location variables.
type LocVar = Var

-- | Abstract region variables.
type RegVar = Var

-- | Type variables that enable polymorphism.
data TyVar = BoundTv Var         -- Type variable bound by a ForAll.
           | SkolemTv String Int -- Skolem constant, the String is just to improve error messages.
           | UserTv Var          -- Used by the parser. Freshen must replace all occurences.
  deriving (Read, Show, Eq, Ord, Generic, NFData)
instance Out TyVar where
  doc (BoundTv v)    = text "b:" PP.<> doc v
  doc (SkolemTv s v) = text s <+> text "sk:" PP.<> doc v
  doc (UserTv v)     = text "u:" PP.<> doc v

  docPrec _ v = doc v

isUserTv :: TyVar -> Bool
isUserTv tv =
  case tv of
    UserTv{} -> True
    _        -> False

--------------------------------------------------------------------------------
-- Gensym monad:

newtype SyM a = SyM (State Int a)
  deriving newtype (Functor, Applicative, Monad, MonadState Int)

instance MonadFail SyM where
  fail = error

-- | A fresh int.
newUniq :: MonadState Int m => m Int
newUniq = state (\x -> (x, x+1))

-- | Generate a unique symbol by attaching a numeric suffix.
gensym :: MonadState Int m => Var -> m Var
gensym v = state (\n -> (cleanFunName v `varAppend` "_" `varAppend` toVar (show n), n + 1))

gensym_tag :: MonadState Int m => Var -> String -> m Var
gensym_tag v str = state (\n -> (cleanFunName v `varAppend` toVar ((show n)++ str) , n + 1))

-- | An infinite alphabet generator: 'a','b', ... ,'z','a0', ...
genLetter :: MonadState Int m => m Var
genLetter = do
    let infStream = cycle ['a'..'z']
    n <- newUniq
    -- Well, this won't give us exactly what the docs say, but it's good
    -- enough and requires no changes to SyM or PassM.
    return $ toVar (infStream !! n : show n)

runSyM :: Int -> SyM a -> (a,Int)
runSyM n (SyM a) = runState a n

--------------------------------------------------------------------------------
-- Pass monad:

-- | The monad used by core Gibbon passes to access 'Config' and other shared state.
newtype PassM a = PassM (ReaderT Config SyM a)
  deriving newtype (Functor, Applicative, Monad, MonadReader Config, MonadState Int)

instance MonadFail PassM where
  fail = error

runPassM :: Config -> Int -> PassM a -> (a,Int)
runPassM cfg cnt (PassM pass) = runSyM cnt (runReaderT pass cfg)

-- | A convenient wrapper over 'runPassM'.
defaultRunPassM :: PassM a -> (a,Int)
defaultRunPassM = runPassM defaultConfig 0

-- | A convenient wrapper over 'runPassM' for running passes in packed mode.
defaultPackedRunPassM :: PassM a -> (a,Int)
defaultPackedRunPassM = runPassM (defaultConfig { dynflags = dflags}) 0
  where dflags = gopt_set Opt_Packed defaultDynFlags

getDynFlags :: MonadReader Config m => m DynFlags
getDynFlags = dynflags <$> ask

getGibbonConfig :: MonadReader Config m => m Config
getGibbonConfig = ask

--------------------------------------------------------------------------------
-- Gibbon config:

-- | Overall configuration of the compiler, as determined by command
-- line arguments and possible environment variables.
data Config = Config
  { input      :: Input
  , mode       :: Mode -- ^ How to run, which backend.
  , benchInput :: Maybe FilePath -- ^ What packed, binary .gpkd file to use as input.
  , arrayInput :: Maybe FilePath -- ^ What array file to use as input.
  , verbosity  :: Int   -- ^ Debugging output, equivalent to DEBUG env var.
  , cc         :: String -- ^ C compiler to use
  , optc       :: String -- ^ Options to the C compiler
  , cfile      :: Maybe FilePath -- ^ Optional override to destination .c file.
  , exefile    :: Maybe FilePath -- ^ Optional override to destination binary file.
  , backend    :: Backend        -- ^ Compilation backend used
  , dynflags   :: DynFlags
  , srcFile    :: Maybe FilePath -- ^ The file being compiled by Gibbon.
  }
  deriving (Show, Read, Eq, Ord)

-- | What input format to expect on disk.
data Input = Haskell
           | SExpr
           | Unspecified
  deriving (Show,Read,Eq,Ord,Enum,Bounded)

-- | How far to run the compiler/interpreter.
data Mode = ToParse  -- ^ Parse and then stop
          | ToC      -- ^ Compile to C
          | ToExe    -- ^ Compile to C then build a binary.
          | RunExe   -- ^ Compile to executable then run.
          | Interp2  -- ^ Interp late in the compiler pipeline.
          | Interp1  -- ^ Interp early.
          | Bench Var -- ^ Benchmark a particular function applied to the packed data within an input file.
          | BenchInput FilePath -- ^ Hardcode the input file to the benchmark in the C code.
  deriving (Show, Read, Eq, Ord)

-- | Compilation backend used
data Backend = C | LLVM
  deriving (Show,Read,Eq,Ord)

defaultConfig :: Config
defaultConfig =
  Config { input = Unspecified
         , mode  = ToExe
         , benchInput = Nothing
         , arrayInput = Nothing
         , verbosity = 1
         , cc = "gcc"
         , optc = " -O3  -flto "
         , cfile = Nothing
         , exefile = Nothing
         , backend = C
         , dynflags = defaultDynFlags
         , srcFile = Nothing
         }

-- | Runtime configuration for executing interpreters.
data RunConfig =
    RunConfig { rcSize  :: Int
              , rcIters :: Word64
              , rcDbg   :: Int
              , rcCursors :: Bool -- ^ Do we support cursors in L1.Exp at this point in the compiler.
              }

defaultRunConfig :: RunConfig
defaultRunConfig = RunConfig { rcSize  = 1
                             , rcIters = 1
                             , rcDbg   = 1
                             , rcCursors = False
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
   [] -> case L.lookup "GIBBON_SIZE" theEnv of
           Nothing -> getRunConfig ["1"]
           Just n  -> getRunConfig [n]
   [sz] -> case L.lookup "GIBBON_ITERS" theEnv  of
             Nothing -> getRunConfig [sz,"1"]
             Just i  -> getRunConfig [sz,i]
   [sz,iters] ->
     return $ RunConfig { rcSize=read sz, rcIters=read iters, rcDbg= dbgLvl, rcCursors= False }
   _ -> error $ "getRunConfig: too many command line args, expected <size> <iters> at most: "++show ls

--------------------------------------------------------------------------------

data SSModality = Read | Write
  deriving (Read, Show, Eq, Ord, Generic, NFData, Out)

-- | An alias for the error function we want to use throughout this project.
{-# INLINE err #-}
err :: HasCallStack => String -> a
err = error

-- | An error that is OUR FAULT, i.e. an internal bug in the compiler.
internalError :: HasCallStack => String -> a
internalError s = error ("internal error: "++s)

instance (Out k,Out v) => Out (Map k v) where
  doc         = doc . M.toList
  docPrec n v = docPrec n (M.toList v)

(#) :: (Ord a, Out a, Out b, Show a, HasCallStack) => Map a b -> a -> b
m # k = case M.lookup k m of
          Just x  -> x
          Nothing -> err $ "Map lookup failed on key: "++show k
                     ++ " in map:\n "++ sdoc m


(!!!) :: (Out a, HasCallStack) => [a] -> Int -> a
ls0 !!! ix0 = go ls0 ix0
 where
   go [] _ = err $ "Not enough elements in list to retrieve "++show ix0
                   ++", list:\n" ++ abbrv 300 ls0
   go (x:_) 0 = x
   go (_:xs) n = go xs (n-1)


fragileZip :: (Show a, Show b, HasCallStack) => [a] -> [b] -> [(a, b)]
fragileZip [] [] = []
fragileZip (a:as) (b:bs) = (a,b) : fragileZip as bs
fragileZip as [] = err$ "fragileZip: right ran out, while left still has: "++show as
fragileZip [] bs = err$ "fragileZip: left ran out, while right still has: "++show bs


-- | Like fragileZip, but takes a custom error message.
fragileZip' :: (Show a, Show b, HasCallStack) => [a] -> [b] -> String -> [(a, b)]
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

lookup3 :: (Eq k, Show k, Show a, Show b) => k -> [(k,a,b)] -> (k,a,b)
lookup3 k ls = go ls
  where
   go [] = error$ "lookup3: key "++show k++" not found in list:\n  "++L.take 80 (show ls)
   go ((k1,a1,b1):r)
      | k1 == k   = (k1,a1,b1)
      | otherwise = go r

fst3 :: (a,b,c) -> a
fst3 (a,_,_) = a

snd3 :: (a,b,c) -> b
snd3 (_,b,_) = b

thd3 :: (a,b,c) -> c
thd3 (_,_,c) = c

cataM
  :: (Monad m, Traversable (Base t), Recursive t)
  => (Base t a -> m a) -> t ->  m a
cataM alg = c where
    c = alg <=< traverse c . project


--------------------------------------------------------------------------------
-- DEBUGGING
--------------------------------------------------------------------------------

theEnv :: [(String, String)]
theEnv = unsafePerformIO getEnvironment

-- | Debugging flag shared by all modules.
--   This is activated by setting the environment variable DEBUG=1..5
dbgLvl :: Int
dbgLvl = case L.lookup "GIBBON_DEBUG" theEnv of
       Nothing  -> defaultDbg
       Just ""  -> defaultDbg
       Just "0" -> defaultDbg
       Just s   ->
         case reads s of
           ((n,_):_) ->
               if n >= minChatLvl
               then trace (" ! Responding to env Var: GIBBON_DEBUG="++s) n
               else n
           [] -> error$"Attempt to parse GIBBON_DEBUG env var as Int failed: "++show s

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

dbgPrintLn :: Int -> String -> IO ()
dbgPrintLn lvl str = dbgPrint lvl (str++"\n")

-- | Conditional version of Debug.Trace.trace
dbgTrace :: Int -> String -> a -> a
dbgTrace lvl msg val =
    if   dbgLvl < lvl
    then val
    else trace msg val

-- | Yo, trace this msg.
dbgTraceIt :: String -> a -> a
dbgTraceIt = trace

-- | Dump some output if the flag is set. Otherwise, do nothing.
dumpIfSet :: Config -> DebugFlag -> String -> IO ()
dumpIfSet cfg flag msg =
  when (dopt flag dflags) $ do
    if not dump_to_file
    then putStrLn msg
    else do
      fp <- case src_file of
              Just fp -> pure $ replaceExtension fp suffix
              Nothing -> do
                n <- randomIO :: IO Int
                let fp = "gibbon-" ++ show n ++ "." ++ suffix
                dbgTraceIt ("dumpIfSet: Got -ddump-to-file, but 'srcFile' is not set in config. Dumping output to " ++ fp) (pure fp)
      withFile fp WriteMode (\h -> hPutStrLn h msg)
  where
    src_file     = srcFile cfg
    dflags       = dynflags cfg
    dump_to_file = dopt Opt_D_DumpToFile dflags
    suffix       = debugFlagSuffix flag

-- A nice filename suffix for each flag.
debugFlagSuffix :: DebugFlag -> String
debugFlagSuffix f =
  case f of
    Opt_D_Dump_Repair   -> "dump-repair"
    Opt_D_Dump_ParAlloc -> "dump-paralloc"
    Opt_D_DumpToFile    -> "dump-to-file" -- This would never be used.
    Opt_D_Dump_Hs       -> "gibbon_hs.hs"

--------------------------------------------------------------------------------
-- Some global constants

-- | For now this is designed to match the Racket output of "#lang
-- gibbon" which itself should change once we implement a custom
-- printer.
truePrinted :: String
truePrinted = "#t"

falsePrinted :: String
falsePrinted = "#f"
