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
directL3 (Prog ddfs fndefs mnExp) = do
    let mnExp' = case mnExp of
                   Nothing -> Nothing
                   Just (ex,ty) -> Just (go ex, ty)
        fndefs' = M.map fd fndefs
    return (Prog ddfs fndefs' mnExp')
  where
    fd :: FunDef1 -> FunDef3
    fd FunDef{funName,funArgs,funTy,funBody} =
        FunDef { funName = funName
               , funTy   = (map goTy $ fst funTy, goTy $ snd funTy)
               , funArgs = funArgs
               , funBody = go funBody }

    go :: L Exp1 -> L Exp3
    go (L p ex) = L p $
      case ex of
        VarE v    -> VarE v
        LitE n    -> LitE n
        LitSymE v -> LitSymE v
        AppE v locs ls   -> AppE v locs $ map go ls
        PrimAppE pr args -> PrimAppE pr $ L.map go args
        LetE (v,locs,ty,rhs) bod -> LetE (v, locs, goTy ty, go rhs) $ go bod
        IfE a b c   -> IfE (go a) (go b) (go c)
        MkProdE ls  -> MkProdE $ L.map go ls
        ProjE i arg -> ProjE i $ go arg
        CaseE scrt ls -> CaseE (go scrt) $ L.map (\(dcon,vs,rhs) -> (dcon,vs,go rhs)) ls
        DataConE loc dcon args -> DataConE loc dcon $ L.map go args
        TimeIt arg ty b -> TimeIt (go arg) ty b
        ParE a b -> ParE (go a) (go b)
        WithArenaE a e -> WithArenaE a $ go e
        Ext _   -> error "directL3: Ext"
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
