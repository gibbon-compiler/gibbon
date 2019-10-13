module Gibbon.Passes.DirectL3
    (directL3) where

import           Data.Loc
import           Data.List as L
import qualified Data.Map as M

import           Gibbon.Common
import           Gibbon.L1.Syntax
import           Gibbon.L3.Syntax


-- | Directly convert the source program to L3. Used in the pointer mode
--
directL3 :: Prog1 -> PassM Prog3
directL3 prg@(Prog ddfs fndefs mnExp) = do
    let mnExp' = case mnExp of
                   Nothing -> Nothing
                   Just (ex,ty) -> Just (go init_fun_env ex, ty)
        fndefs' = M.map fd fndefs
    return (Prog ddfs fndefs' mnExp')
  where
    init_fun_env = progToEnv prg

    fd :: FunDef1 -> FunDef3
    fd FunDef{funName,funArgs,funTy,funBody} =
        let env2 = extendsVEnv (M.fromList $ zip funArgs (fst funTy)) init_fun_env in
        FunDef { funName = funName
               , funTy   = (map goTy $ fst funTy, goTy $ snd funTy)
               , funArgs = funArgs
               , funBody = go env2 funBody }

    go :: Env2 Ty1 -> L Exp1 -> L Exp3
    go env2 (L p ex) = L p $
      case ex of
        VarE v    -> VarE v
        LitE n    -> LitE n
        LitSymE v -> LitSymE v
        AppE v locs ls   -> AppE v locs $ map (go env2) ls
        PrimAppE pr args -> PrimAppE pr $ L.map (go env2) args
        LetE (v,locs,ty,rhs) bod -> LetE (v, locs, goTy ty, go env2 rhs) $
                                      go (extendVEnv v ty env2) bod
        IfE a b c   -> IfE (go env2 a) (go env2 b) (go env2 c)
        MkProdE ls  -> MkProdE $ L.map (go env2) ls
        ProjE i arg -> ProjE i $ go env2 arg
        CaseE scrt ls -> CaseE (go env2 scrt) $
                           L.map (\(dcon,vs,rhs) -> (dcon,vs,go env2 rhs)) ls
        DataConE loc dcon args -> DataConE loc dcon $ L.map (go env2) args
        TimeIt arg ty b -> TimeIt (go env2 arg) ty b
        ParE ls -> ParE $ map (go env2) ls
        WithArenaE a e -> WithArenaE a $ go env2 e
        Ext (BenchE fn _locs args b) ->
          let fn_ty  = lookupFEnv fn env2
              ret_ty = snd fn_ty
              ex'    = l$ TimeIt (l$ AppE fn [] args) ret_ty b
          in unLoc $ go env2 ex'
        MapE{}  -> error "directL3: todo MapE"
        FoldE{} -> error "directL3: todo FoldE"

    goTy :: Ty1 -> Ty3
    goTy ty =
      case ty of
        IntTy -> IntTy
        SymTy -> SymTy
        BoolTy -> BoolTy
        ProdTy tys -> ProdTy $ map goTy tys
        SymDictTy mv _ty -> SymDictTy mv CursorTy
        PackedTy _ _ -> CursorTy
        ArenaTy -> ArenaTy
        ListTy _ -> error "directL3: todo ListTy"
        PtrTy -> PtrTy
        CursorTy -> CursorTy
