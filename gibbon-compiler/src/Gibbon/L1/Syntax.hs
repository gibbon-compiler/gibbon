{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | The source language for recursive tree traversals.
--   This is a first-order language for the "closed world" scenario:
--   not integrating with a functional host language, but rather
--   genarating C code like a DSL.

module Gibbon.L1.Syntax
    (
      -- * Core types specific to L1
      Prog1, FunDef1, FunDefs1, DDef1, DDefs1, Exp1, Ty1, NoExt

    , module Gibbon.Language
    ) where

import Control.DeepSeq ( NFData )
import Data.Loc
import Data.Set as S
import GHC.Generics
import Text.PrettyPrint.GenericPretty

import Gibbon.Language

--------------------------------------------------------------------------------

instance FunctionTy Ty1 where
  -- | At this stage, function types are just (in , out) tuples.
  type ArrowTy Ty1 = ([Ty1] , Ty1)
  inTys = fst
  outTy = snd

-- | A convenient, default instantiation of the L1 expression type.
type Exp1 = PreExp NoExt () Ty1

-- | An L1 program.
type Prog1 = Prog (L Exp1)

-- | Datatypes
type DDefs1 = DDefs Ty1
type DDef1  = DDef Ty1

-- | Function definition used in L1 programs.
type FunDef1 = FunDef (L Exp1)

type FunDefs1 = FunDefs (L Exp1)

-- | The type rperesentation used in L1.
type Ty1 = UrTy ()


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
instance FreeVars (NoExt l d) where
  gFreeVars _ = S.empty

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
instance HasSimplifiableExt NoExt l d => SimplifiableExt (L (PreExp NoExt l d)) (NoExt l d) where
  gInlineTrivExt _ impossible = impossible

-- | A dummy instance for "no-extension" extension point.
instance HasSubstitutableExt NoExt l d => SubstitutableExt (L (PreExp NoExt l d)) (NoExt l d) where
  gSubstExt _ _ impossible  = impossible
  gSubstEExt _ _ impossible = impossible

-- | A dummy instance for "no-extension" extension point.
instance Typeable (NoExt l d) where
  gRecoverType _ _ _ = error "<NoExt: It should be impossible to recover type of this>"

-- | A dummy instance for "no-extension" extension point.
instance Renamable (NoExt l d) where
  gRename _ impossible = impossible
