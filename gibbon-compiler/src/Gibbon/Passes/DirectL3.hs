module Gibbon.Passes.DirectL3
    (directL3) where

import Data.Loc
import Data.List as L
import Data.Map as M

import Gibbon.L1.Syntax
import Gibbon.L2.Syntax (stripTyLocs)
import qualified Gibbon.L3.Syntax as L3


-- | Directly convert the source program to L3. Used in the pointer mode
--
directL3 :: Prog -> L3.Prog
directL3 (Prog ddfs fndefs mnExp) = do
    let mnExp' = case mnExp of
                   Nothing -> Nothing
                   Just (ex,ty) -> Just (go ex, stripTyLocs ty)

        fds = L.map fd $ M.elems fndefs
        fndefs' = M.fromList $ L.map (\f -> (L3.funName f, f)) fds
    L3.Prog ddfs fndefs' mnExp'
  where
    fd :: FunDef -> L3.FunDef
    fd FunDef{funName,funArg,funTy,funBody} =
        let (argty,retty) = funTy
        in L3.FunDef { L3.funName = funName
                     , L3.funTy   = (toL3Ty argty, toL3Ty retty)
                     , L3.funArg  = funArg
                     , L3.funBody = go funBody
                     }

    toL3Ty :: Ty1 -> L3.Ty3
    toL3Ty = stripTyLocs

    go :: L Exp1 -> L L3.Exp3
    go (L p ex) = L p $
      case ex of
        VarE v    -> VarE v
        LitE n    -> LitE n
        LitSymE v -> LitSymE v
        AppE v locs arg  -> AppE v locs $ go arg
        PrimAppE pr args -> PrimAppE pr $ L.map go args
        LetE (v,locs,ty,rhs) bod -> LetE (v,locs,toL3Ty ty, go rhs) $ go bod
        IfE a b c   -> IfE (go a) (go b) (go c)
        MkProdE ls  -> MkProdE $ L.map go ls
        ProjE i arg -> ProjE i $ go arg
        CaseE scrt ls -> CaseE (go scrt) $ L.map (\(dcon,vs,rhs) -> (dcon,vs,go rhs)) ls
        DataConE loc dcon args -> DataConE loc dcon $ L.map go args
        TimeIt arg ty b -> TimeIt (go arg) ty b
        Ext _   -> error "directL3: Ext"
        MapE{}  -> error "directL3: todo MapE"
        FoldE{} -> error "directL3: todo FoldE"
