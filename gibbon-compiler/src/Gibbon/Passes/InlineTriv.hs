{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}

-- | Compiler pass to inline trivials.
module Gibbon.Passes.InlineTriv (inlineTriv, inlineTrivExp) where

import           Data.Loc
import qualified Data.Map as M
import           Prelude hiding (exp)

import           Gibbon.Common
import           Gibbon.Language.Syntax

--------------------------------------------------------------------------------

-- | Inline trivial let bindings (binding a var to a var or int), mainly to clean up
--   the output of `flatten`.
inlineTriv :: (HasSimplifiable e l d)
           => Prog (L (PreExp e l d)) -> PassM (Prog (L (PreExp e l d)))
inlineTriv (Prog ddefs funs main) =
    return (Prog ddefs (fmap (inlineTrivFun . inlineTrivFun) funs) main')
  where
    inlineTrivFun (FunDef nam narg ty bod) =
      FunDef nam narg ty (inlineTrivExp M.empty bod)

    main' = case main of
              Nothing -> Nothing
              Just (m,ty) -> Just (inlineTrivExp M.empty m, ty)

type ExpEnv e l d = M.Map Var (L (PreExp e l d))

inlineTrivExp :: forall e l d. HasSimplifiable e l d
              => ExpEnv e l d -> L (PreExp e l d) -> L (PreExp e l d)
inlineTrivExp = go
  where
  go :: ExpEnv e l d -> L (PreExp e l d) -> (L (PreExp e l d))
  go env (L p0 e0) = L p0 $
    case e0 of
      VarE v    -> case M.lookup v env of
                     Nothing -> VarE v
                     Just e  -> unLoc e
      Ext ext   -> Ext $ gInlineTrivExt env ext
      LitE{}    -> e0
      LitSymE{} -> e0

      AppE v lvs es -> AppE v lvs $ map (go env) es
      PrimAppE p es -> PrimAppE p $ map (go env) es

      LetE (v,lvs,t,e') e ->
       case e' of
         L _ (VarE v') ->
           case M.lookup v' env of
             Nothing -> unLoc $ go (M.insert v e' env) e
             Just pr -> unLoc $ go (M.insert v pr env) e
         et | isTrivial et ->
                -- Apply existing renames:
                let et' = go env et in
                unLoc $ go (M.insert v et' env) e
         _ -> LetE (v,lvs,t,go env e') (go env e)

      IfE e1 e2 e3 -> IfE (go env e1) (go env e2) (go env e3)

      -- TODO: Type check here:
      ProjE i e -> unLoc $ mkProj i $ go env e

      MkProdE es -> MkProdE $ map (go env) es
      CaseE e mp ->
       let e' = go env e
           mp' = map (\(c,args,ae) -> (c,args,go env ae)) mp
       in CaseE e' mp'

      DataConE loc c es -> DataConE loc c $ map (go env) es
      TimeIt e t b -> TimeIt (go env e) t b
      SpawnE w fn locs args -> SpawnE w fn locs $ map (go env) args
      SyncE -> SyncE
      WithArenaE v e -> WithArenaE v (go env e)
      MapE (v,t,e') e -> MapE (v,t,go env e') (go env e)
      FoldE (v1,t1,e1) (v2,t2,e2) e3 ->
       FoldE (v1,t1,go env e1) (v2,t2,go env e2) (go env e3)

instance HasSimplifiable e l d => Simplifiable (L (PreExp e l d)) where
  gInlineTrivExp = inlineTrivExp
