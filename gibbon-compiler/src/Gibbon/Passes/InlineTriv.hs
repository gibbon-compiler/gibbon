
-- | Compiler pass to inline trivials.
module Gibbon.Passes.InlineTriv (inlineTriv, inlineTrivExp) where

import           Data.Loc
import           Prelude hiding (exp)
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common
import           Gibbon.GenericOps (isTrivial)
import           Gibbon.GenericOps (NoExt)
import           Gibbon.L1.Syntax as L1 hiding (mkProj)

-- import Gibbon.Passes.Flatten (typeExp, TEnv)


-- | Inline trivial let bindings (binding a var to a var or int), mainly to clean up
--   the output of `flatten`.
inlineTriv :: Prog1 -> PassM Prog1
inlineTriv (Prog ddefs funs main) =
    return (Prog ddefs (fmap inlineTrivFun funs) main')
  where
    inlineTrivFun (FunDef nam narg (targ, ty) bod) =
      FunDef nam narg (targ, ty) (inlineTrivExp ddefs bod)
    main' = case main of
              Nothing -> Nothing
              Just (m,ty) -> Just (inlineTrivExp ddefs m, ty)


type MyExp l = L (PreExp NoExt l (UrTy l))
type Env l = [(Var, (UrTy l, MyExp l))]

inlineTrivExp :: forall l a . (Out l, Show l)
              => DDefs a -> MyExp l -> MyExp l
inlineTrivExp _ddefs = go []
  where

  -- Just a hook for debugging:
  go :: Env l -> MyExp l -> MyExp l
  go env e  = exp env e

  -- | Here we go to some lengths to maintain the syntactic invariants
  -- for the extended L2 forms. The idea is that we can only reference
  -- variables within these forms, but we still must apply the
  -- environment because the old bindings have been removed.
  --
  -- An alternative would be to let the extended forms disappear at
  -- this point, and handle them at the level of "AppE" in Lower.hs.
  _withVar :: Env l -> Var -> (Var -> MyExp l) -> MyExp l
  _withVar env v fn =
    case lookup v env of
      Nothing        -> fn v
      Just (_, (L _ (VarE v2))) -> fn v2
      -- fixme, need gensym:
      Just (ty,oth)  -> L NoLoc $ LetE (v,[],ty,oth) $ fn v

  exp :: Env l -> MyExp l -> (MyExp l)
  exp env (L p0 e0) = L p0 $
    case e0 of
      Ext _  -> e0
      VarE v -> case lookup v env of
                    Nothing -> VarE v
                    Just (_,e) -> unLoc e
      LitE i -> LitE i
      LitSymE v -> LitSymE v

      AppE v lvs e -> AppE v lvs $ go env e
      PrimAppE p es -> PrimAppE p $ map (go env) es

      LetE (v,lvs,t,e') e ->
       case e' of
         L _ (VarE v') ->
           case lookup v' env of
             Nothing -> unLoc $ go ((v,(t,e')):env) e
             Just pr -> unLoc $ go ((v,pr):env) e
         et | isTrivial et ->
                -- Apply existing renames:
                let et' = go env et in
                unLoc $ go ((v,(t,et')):env) e
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
      ParE a b -> ParE (go env a) (go env b)
      MapE (v,t,e') e -> MapE (v,t,go env e') (go env e)
      FoldE (v1,t1,e1) (v2,t2,e2) e3 ->
       FoldE (v1,t1,go env e1) (v2,t2,go env e2) (go env e3)

      {-
      -- FIXME: Remove:
      L2.NewBuffer -> L2.NewBuffer
      L2.ReadInt v     -> unLoc $ withVar env v $ \v2 -> L NoLoc $ L2.ReadInt v2
      L2.WriteInt v e  -> unLoc $ withVar env v $ \v2 -> L NoLoc $
                                                         L2.WriteInt v2 (go env e)
      L2.AddCursor v i -> unLoc $ withVar env v $ \v2 -> L NoLoc $ L2.AddCursor v2 i

      p | L2.isExtendedPattern p ->
          internalError $ "InlineTriv: failed to handle extended L2 form: "
          ++ndoc p++", env: "++ndoc env
      -}

-- Helpers which do opportunistic reduction:

mkProj :: Int -> MyExp l -> MyExp l
mkProj ix (L _ (MkProdE ls)) = ls !! ix
mkProj ix e@(L p _) = L p $ ProjE ix e
