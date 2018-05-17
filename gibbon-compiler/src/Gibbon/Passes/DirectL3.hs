module Gibbon.Passes.DirectL3
    (directL3) where

import Control.Monad.Except
import Data.Loc
import Data.List as L
import Data.Map as M

import Gibbon.Common
import Gibbon.L1.Syntax
import Gibbon.L1.Typecheck
import Gibbon.L2.Syntax (stripTyLocs)
import qualified Gibbon.L3.Syntax as L3


-- | Directly convert the source program to L3. Used in the pointer mode
--
directL3 :: Prog -> L3.Prog
directL3 prg@(Prog ddfs fndefs mnExp) = do
    let mnExp' = case mnExp of
                   Nothing -> Nothing
                   Just ex -> do
                       ty <- return $ runExcept $ tcExp ddfs (progToEnv prg) ex
                       case ty of
                         Left err -> error $ show err
                         Right ty' -> Just (go ex, ty')

        fds = L.map fd $ M.elems fndefs
        fndefs' = M.fromList $ L.map (\f -> (L3.funname f, f)) fds
    L3.Prog ddfs fndefs' mnExp'
  where
    fd :: FunDef Ty1 (L Exp1) -> L3.FunDef
    fd FunDef{funName,funArg,funRetTy,funBody} =
        let (arg,ty) = funArg
        in L3.FunDef { L3.funname = funName
                     , L3.funty = L3.ArrowTy (toL3Ty ty) (toL3Ty funRetTy)
                     , L3.funarg = arg
                     , L3.funbod = go funBody
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
