-- | Mark structure-preserving fully-factored traversals so later passes can
-- selectively share dead scalar SoA buffers.  The standalone optimization
-- intentionally does not mark dcon-buffer sharing; recursive traversals still
-- rely on the dcon stream to drive control flow.
module Gibbon.Passes.SelectiveBufferSharing
  ( selectiveBufferSharing
  ) where

import qualified Data.Map as M

import Gibbon.Common
import Gibbon.Language
import Gibbon.L2.Syntax

selectiveBufferSharing :: Prog2 -> PassM Prog2
selectiveBufferSharing prog@Prog{ddefs, fundefs} = do
  fds' <- mapM (rewriteFun ddefs) (M.elems fundefs)
  pure $ prog { fundefs = M.fromList [ (funName f, f) | f <- fds' ] }

rewriteFun :: DDefs Ty2 -> FunDef2 -> PassM FunDef2
rewriteFun ddefs fn@FunDef{funTy, funMeta, funBody}
  | SelectiveBufferSharing `notElem` funOpt funMeta = pure fn
  | otherwise =
      case eligibleTyCon ddefs funTy of
        Nothing -> pure fn
        Just tycon ->
          pure $ fn { funBody = rewriteExp ddefs tycon Nothing funBody }

eligibleTyCon :: DDefs Ty2 -> ArrowTy2 Ty2 -> Maybe TyCon
eligibleTyCon ddefs ArrowTy2{arrIns, arrOut} =
  case ([ tycon | PackedTy tycon _ <- arrIns ], arrOut) of
    ([inTyCon], PackedTy outTyCon _)
      | inTyCon == outTyCon
      , memLayout (lookupDDef ddefs inTyCon) == FullyFactored
      -> Just inTyCon
    _ -> Nothing

rewriteExp :: DDefs Ty2 -> TyCon -> Maybe (Var, DataCon, [Var], [Ty2]) -> Exp2 -> Exp2
rewriteExp ddefs tycon ctx ex =
  case ex of
    VarE{} -> ex
    LitE{} -> ex
    CharE{} -> ex
    FloatE{} -> ex
    LitSymE{} -> ex
    AppE f cty locs args -> AppE f cty locs (map goNoCtx args)
    PrimAppE p args -> PrimAppE p (map goNoCtx args)
    MkProdE ls -> MkProdE (map goNoCtx ls)
    ProjE i e -> ProjE i (goNoCtx e)
    IfE a b c -> IfE (goNoCtx a) (goNoCtx b) (goNoCtx c)
    LetE (v, locs, ty, rhs) bod ->
      LetE (v, locs, ty, goNoCtx rhs) (rewriteExp ddefs tycon ctx bod)
    CaseE scrt brs ->
      let scrutVar = case scrt of
            VarE v -> Just v
            _ -> Nothing
          rewriteBranch (dcon, vlocs, rhs) =
            let vars = map fst vlocs
                tys = lookupDataCon ddefs dcon
                ctx' = (\v -> (v, dcon, vars, tys)) <$> scrutVar
             in (dcon, vlocs, rewriteExp ddefs tycon ctx' rhs)
       in CaseE (goNoCtx scrt) (map rewriteBranch brs)
    DataConE sloc dcon args ->
      let args' = map goNoCtx args
       in case ctx of
            Just (src, branchDcon, branchVars, branchTys)
              | branchDcon == dcon
              , getTyOfDataCon ddefs dcon == tycon
              ->
                  let shareTargets =
                        [ ShareScalarFieldBuffer dcon idx
                        | (idx, (arg, ty, branchVar)) <- zip [0..] (zip3 args' branchTys branchVars)
                        , isScalarTy ty
                        , arg == VarE branchVar
                        ]
                   in if null shareTargets
                        then DataConE sloc dcon args'
                        else Ext $ SelectiveBufferShareE src shareTargets (DataConE sloc dcon args')
            _ -> DataConE sloc dcon args'
    TimeIt e ty b -> TimeIt (goNoCtx e) ty b
    WithArenaE v e -> WithArenaE v (goNoCtx e)
    SpawnE f locs args -> SpawnE f locs (map goNoCtx args)
    SyncE -> SyncE
    MapE (f, ty, e1) e2 -> MapE (f, ty, goNoCtx e1) (goNoCtx e2)
    FoldE (f1, t1, e1) (f2, t2, e2) e3 -> FoldE (f1, t1, goNoCtx e1) (f2, t2, goNoCtx e2) (goNoCtx e3)
    Ext ext ->
      case ext of
        LetRegionE r sz endmut ty bod -> Ext $ LetRegionE r sz endmut ty (rewriteExp ddefs tycon ctx bod)
        LetParRegionE r sz ty bod -> Ext $ LetParRegionE r sz ty (rewriteExp ddefs tycon ctx bod)
        LetLocE l rhs bod -> Ext $ LetLocE l rhs (rewriteExp ddefs tycon ctx bod)
        LetRegE l rhs bod -> Ext $ LetRegE l rhs (rewriteExp ddefs tycon ctx bod)
        IndirectionE tc dc from to fallback ->
          Ext $ IndirectionE tc dc from to (goNoCtx fallback)
        LetAvail vs bod -> Ext $ LetAvail vs (rewriteExp ddefs tycon ctx bod)
        SelectiveBufferShareE src tgts bod ->
          Ext $ SelectiveBufferShareE src tgts (rewriteExp ddefs tycon ctx bod)
        _ -> ex
  where
    goNoCtx = rewriteExp ddefs tycon Nothing
