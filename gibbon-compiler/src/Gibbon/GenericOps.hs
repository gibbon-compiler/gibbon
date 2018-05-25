{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveAnyClass #-}

-- | Generic operations that are supported by the various intermediate
-- representations inside the compiler.

module Gibbon.GenericOps
    ( Interp(..)

    -- * Free Variables, generic interface
    , FreeVars(..)

    -- * Genereric interface for expressions and select passes
    , Expression(..), NoExt
    , Flattenable(..)
    , Simplifiable(..)
    , Typeable(..)
    )
    where

import Control.DeepSeq (NFData)
import Data.Loc
import GHC.Generics
import Text.PrettyPrint.GenericPretty
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Set as S
import qualified Data.ByteString.Lazy.Char8 as B

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

-------------------------------------------------------------------------------
-- Free Variables
-------------------------------------------------------------------------------

-- | Expression and program types which support a notion of free variables.
class FreeVars a where
    -- | Return a set of free TERM variables.  Does not return location variables.
    gFreeVars :: a -> S.Set Var

instance FreeVars (NoExt l d) where
  gFreeVars _ = S.empty

instance FreeVars e => FreeVars (L e) where
  gFreeVars (L _ e) = gFreeVars e

-------------------------------------------------------------------------------
-- Compiler passes used in multiple phases
-------------------------------------------------------------------------------

-- | A generic interface to expressions found in different phases of
-- the compiler.
class (Show e, Out e, FreeVars e) => Expression e where
  -- | The type representation used in this expression.
  type TyOf e
  -- | The location (variable) representation used in this expression.
  type LocOf e
  -- | Is an expression considered trivial (duplicatable by the compiler)?
  isTrivial :: e -> Bool

-- | IRs amenable to flattening
class Expression e => Flattenable e where
  -- | Process an expression into a fully-flattened expression which typically includes a
  -- larger number of temporary, local variable bindings.
  gFlattenExp :: DDefs (TyOf e) -> Env2 (TyOf e) -> e -> SyM e

  -- | A private method.  Gather the bindings from a subexpression,
  -- but do not "discharge" them by creating a let expression.  They
  -- are in order, so later may depend on earlier.
  gFlattenGatherBinds :: DDefs (TyOf e) -> Env2 (TyOf e) -> e -> SyM ([Binds e],e)

type Binds e = (Var,[LocOf e],TyOf e, e)

-- | IRs amenable to simplification/inlineTrivs
class Expression e => Simplifiable e where
  gInlineTrivExp :: DDefs (TyOf e) -> e -> e

-- | This is NOT a replacement for any typechecker. This is supposed to be used just to
-- recover the type of an expression in a type-environment
-- Without this, we cannot have truly generic implementation of the Flattenable class,
-- since we need to know the type of an expression before we discharge it with a LetE
class Expression e => Typeable e where
  gTypeExp :: DDefs (TyOf e) -> Env2 (TyOf e) -> e -> TyOf e

--------------------------------------------------------------------------------

-- | An uninhabidited type indicating that the base grammar is not extended with any
-- additional constructs.
data NoExt l d   deriving (Generic, NFData)

instance Show (NoExt l d) where
  show _ = error "<NoExt: This should be impossible to print>"
instance Out (NoExt l d) where
  doc _ = error "<NoExt: This should be impossible to print>"
  docPrec _ x = doc x
instance Read (NoExt l d) where
  readsPrec _ = error "<NoExt: This should be impossible to read>"
instance Eq (NoExt l d) where
  _ == _ = True
instance Ord (NoExt l d) where
  compare _ _ = EQ

-- | A dummy instance for "no-extension" extension point.
instance Expression (NoExt l d) where
  type TyOf  (NoExt l d) = d
  type LocOf (NoExt l d) = l
  isTrivial _ = True

-- | A dummy instance for "no-extension" extension point.
instance Flattenable (NoExt l d) where
  gFlattenExp _ _ impossible = return impossible
  gFlattenGatherBinds  _ _ impossible = return ([],impossible)

-- | A dummy instance for "no-extension" extension point.
instance Simplifiable (NoExt l d) where
  gInlineTrivExp _ impossible = impossible

-- | A dummy instance for "no-extension" extension point.
instance Typeable (NoExt l d) where
  gTypeExp _ _ _ = error "<NoExt: It should be impossible to recover type of this>"
