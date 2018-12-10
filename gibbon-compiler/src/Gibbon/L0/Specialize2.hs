{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{- L0 Specializer (part 2):
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Paulette worked on a specializer which lives in 'Gibbon.L0.Specialize'
and specializes functions on curried calls. Now we need a driver which
takes these different pieces, and puts them together in order to
transform a fully polymorphic L0 program, into a monomorphic L1 program.
This module is the first attempt to do that.

-}

module Gibbon.L0.Specialize2 where

import           Control.Monad.State
import qualified Data.Map as M

import           Gibbon.Common
import           Gibbon.L0.Syntax as L0
import           Gibbon.L1.Syntax as L1

--------------------------------------------------------------------------------

type TvSubstEnv = M.Map TyVar Ty1

data SpecState = SpecState
  { spec_ddefs :: M.Map Var [TvSubstEnv] }
  deriving (Show, Read, Eq, Ord)

newtype SpecM a = SpecM (StateT SpecState PassM a)
  deriving (Functor, Applicative, Monad, MonadState SpecState)

runSpecM :: SpecState -> SpecM a -> PassM (a, SpecState)
runSpecM st (SpecM m) = runStateT m st

--------------------------------------------------------------------------------

-- | Only specializes datatypes for now.
specializeProg :: Prog0 -> PassM Prog1
specializeProg = __

-- | Replace all type variables in a datatype with a concrete type.
specializeDDefWith :: TvSubstEnv -> DDef0 -> DDef1
specializeDDefWith = __

-- | Traverse a program, and replace callsites of polymorphic data constructors
-- with their monomorphic counterpart i.e (Just 3) becomes (Just_Int 3) and so on.
-- This function just records the fact that we need a 'Maybe' type specialized
-- to an Int, but doesn't create it. The caller is responsible for ensuring
-- that the appropriate monomorphic datatype is created.
collectDDefInstances :: Exp0 -> SpecM Exp0
collectDDefInstances ex = __

-- specializeDDefs :: L0.Exp0 -> L0.Exp0
-- specializeDDefs = __
