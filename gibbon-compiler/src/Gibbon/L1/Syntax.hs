{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances  #-}


-- | The source language for recursive tree traversals.
--   This is a first-order language for the "closed world" scenario:
--   not integrating with a functional host language, but rather
--   genarating C code like a DSL.
module Gibbon.L1.Syntax
      -- * Core types specific to L1
  ( Prog1
  , FunDef1
  , FunDefs1
  , DDef1
  , DDefs1
  , Exp1
  , Ty1
  , E1Ext(..)
  , module Gibbon.Language
  ) where

import           Control.DeepSeq                (NFData)
import           Data.Graph                     as G
import qualified Data.Map                       as M
import qualified Data.Set                       as S
import           GHC.Generics
import           Prelude                        as P
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common
import           Gibbon.Language


--------------------------------------------------------------------------------
instance FunctionTy Ty1
  -- | At this stage, function types are just (in , out) tuples.
                                                                 where
  type ArrowTy Ty1 = ([Ty1], Ty1)
  inTys            = fst
  outTy            = snd


-- | A convenient, default instantiation of the L1 expression type.
type Exp1 = PreExp E1Ext () Ty1


-- | An L1 program.
type Prog1 = Prog Exp1


-- | Datatypes
type DDefs1 = DDefs Ty1

type DDef1 = DDef Ty1


-- | Function definition used in L1 programs.
type FunDef1 = FunDef Exp1

type FunDefs1 = FunDefs Exp1


-- | The type rperesentation used in L1.
type Ty1 = UrTy ()

{-
Type CFGfunctionMap: Mapping from function definition, to the control flow graph of the program.
Edge : A tuple of expression and its likelihood.
See Data.Graph in containers for more definitions.
TODO: The functions for which the CFG should be annoted at the front-end level and they should be passable to this pass.
Only generate CFG for functions which are annotated.
-}
--type CFGfunctionMap = M.Map FunDef1 (G.Graph, G.Vertex -> ( (Exp1, Integer), Integer, [Integer]), Integer -> Maybe G.Vertex)
{- A Map storing a function to its data flow graph (Use-def chains) -}
{- Var -- function name -}
{- node = (Var, Exp1, TyCon), ie, variable that's assigned and the assignment expression and type of the variable -}
{- key = Exp1, The expression is the key itself -}
--type DefUseChainsFunctionMap = M.Map Var (G.Graph, G.Vertex -> ((Var, Exp1, TyCon), Exp1, [Exp1]), Exp1 -> Maybe G.Vertex)

--------------------------------------------------------------------------------

data E1Ext loc dec = BenchE Var [loc] [(PreExp E1Ext loc dec)] Bool
                   | AddFixed Var Int     -- Created by AddRAN.
                   | StartOfPkdCursor Var -- Created by AddRAN.
  deriving (Show, Ord, Eq, Read, Generic, NFData, Out)

instance (Out l, Out d) => FreeVars (E1Ext l d) where
  gFreeVars e =
    case e of
      BenchE _ _ args _-> S.unions (map gFreeVars args)
      AddFixed v _ -> S.singleton v
      StartOfPkdCursor cur -> S.singleton cur

instance (Show l, Show d, Out l, Out d) => Expression (E1Ext l d)
 where
  type TyOf (E1Ext l d)  = d
  type LocOf (E1Ext l d) = l
  isTrivial _            = False

instance (Show l, Show d, Out l, Out d) => Flattenable (E1Ext l d)
 where
  gFlattenGatherBinds _ddfs _env ex = return ([], ex)
  gFlattenExp _ddfs _env ex         = return ex

instance HasSimplifiableExt E1Ext l d =>
         SimplifiableExt (PreExp E1Ext l d) (E1Ext l d)
 where
  gInlineTrivExt _env ext = ext

instance HasSubstitutableExt E1Ext l d =>
         SubstitutableExt (PreExp E1Ext l d) (E1Ext l d) where
  gSubstExt old new ext =
    case ext of
      BenchE fn tyapps args b -> BenchE fn tyapps (map (gSubst old new) args) b
      AddFixed v i -> if v == old
                      then case new of
                             (VarE v') -> AddFixed v' i
                             _oth -> error "Could not substitute non-variable in AddFixed"
                      else AddFixed v i
      StartOfPkdCursor cur ->
                     if cur == old
                     then case new of
                             VarE cur' -> StartOfPkdCursor cur'
                             _oth -> error "Could not substitute non-variable in StartOfPkdCursor"
                     else (StartOfPkdCursor cur)

  gSubstEExt old new ext =
    case ext of
      BenchE fn tyapps args b ->
        BenchE fn tyapps (P.map (gSubstE old new) args) b
      AddFixed v i -> AddFixed v i
      StartOfPkdCursor cur  -> StartOfPkdCursor cur

instance Typeable (E1Ext () (UrTy ())) where
  gRecoverType _ddefs env2 ext =
    case ext of
      BenchE fn _ _ _ -> outTy $ fEnv env2 # fn
      AddFixed v _i   -> if M.member v (vEnv env2)
                         then CursorTy
                         else error $ "AddFixed: unbound variable " ++ show v
      StartOfPkdCursor cur ->
                         case M.lookup cur (vEnv env2) of
                           Just (PackedTy{}) -> CursorTy
                           ty -> error $ "StartOfPkdCursor: got " ++ show ty

instance Renamable ()
 where
  gRename _ () = ()

instance HasRenamable E1Ext l d => Renamable (E1Ext l d) where
  gRename env ext =
    case ext of
      BenchE fn tyapps args b -> BenchE fn tyapps (map go args) b
      AddFixed v i -> AddFixed (go v) i
      StartOfPkdCursor cur -> StartOfPkdCursor (go cur)
    where
      go ::
           forall a. Renamable a
        => a
        -> a
      go = gRename env
