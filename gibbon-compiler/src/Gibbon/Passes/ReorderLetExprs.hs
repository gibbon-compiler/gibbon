module Gibbon.Passes.ReorderLetExprs (reorderLetExprs) where

import qualified Data.List as L 
import qualified Data.Set as S

import qualified Data.Map as M

import Data.Foldable as F
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.L2.Syntax
import Data.Maybe ()
import qualified Data.Maybe as S


data DelayedExpr = LetExpr (Var, [LocVar], Ty2, Exp2)
                 | LetLocExpr LocVar LocExp 

type DefinedVars = S.Set FreeVarsTy
type DelayedExprMap = M.Map DefinedVars DelayedExpr

reorderLetExprs :: Prog2 -> PassM Prog2
reorderLetExprs (Prog ddefs fundefs mainExp) = do
    fds' <- mapM reorderLetExprsFun (M.elems fundefs)
    let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
    mainExp' <- case mainExp of
                    Just (e,ty) -> do
                                      e' <- reorderLetExprsFunBody S.empty M.empty e
                                      pure $ Just (e', ty)
                    Nothing     -> pure Nothing
    pure $ Prog ddefs fundefs' mainExp'

reorderLetExprsFun :: FunDef2 -> PassM FunDef2
reorderLetExprsFun f@FunDef{funName,funTy,funArgs,funBody,funMeta} = do
    let definedVars = S.fromList $ map (fromVarToFreeVarsTy) funArgs
    funBody' <- reorderLetExprsFunBody definedVars M.empty funBody
    pure $ f { funBody = funBody' }


{- We also need to release let expressions which are defined -}
reorderLetExprsFunBody :: DefinedVars -> DelayedExprMap -> Exp2 -> PassM Exp2
reorderLetExprsFunBody definedVars delayedExprMap ex = do
    case ex of
        LetE (v,locs,ty,rhs) bod -> do
            let freeVarsRhs = allFreeVars rhs 
            {- Check if variables in rhs are in the DefinedVars-}
                isDefined = S.isSubsetOf freeVarsRhs definedVars
              in if isDefined 
                 then do
                    let definedVars' = S.insert (fromVarToFreeVarsTy v) definedVars
                    bod' <- reorderLetExprsFunBody definedVars' delayedExprMap bod 
                    {- Check which expressions can be released -}
                    
                    pure $ LetE (v, locs, ty, rhs) bod'
                 else do
                    let delayedLetE = LetExpr (v, locs, ty, rhs)
                        delayedExprMap' = M.insert freeVarsRhs delayedLetE delayedExprMap
                    bod' <- reorderLetExprsFunBody definedVars delayedExprMap' bod
                    pure bod'
        
        LitE _ -> pure ex
        CharE _ -> pure ex
        FloatE{} -> pure ex
        LitSymE _ -> pure ex
        VarE _ -> pure ex
        LitSymE _ -> pure ex

        AppE f lvs ls -> AppE f lvs <$> mapM (reorderLetExprsFunBody definedVars delayedExprMap) ls

        PrimAppE p ls -> PrimAppE p <$> mapM (reorderLetExprsFunBody definedVars delayedExprMap) ls

        MkProdE ls -> MkProdE <$> mapM (reorderLetExprsFunBody definedVars delayedExprMap) ls 
        
        DataConE loc k ls -> DataConE loc k <$> mapM (reorderLetExprsFunBody definedVars delayedExprMap) ls
        
        IfE a b c -> do
            a' <- reorderLetExprsFunBody definedVars delayedExprMap a
            b' <- reorderLetExprsFunBody definedVars delayedExprMap b
            c' <- reorderLetExprsFunBody definedVars delayedExprMap c
            pure $ IfE a' b' c' 

        ProjE i e -> do
            e' <- reorderLetExprsFunBody definedVars delayedExprMap e
            pure $ ProjE i e'

        CaseE e ls -> do 
            e' <- reorderLetExprsFunBody definedVars delayedExprMap e
            ls' <- mapM (\(dcon, vs, rhs) -> do
                            let definedVars' = S.union definedVars (S.fromList (map (fromVarToFreeVarsTy . fst) vs))
                            rhs' <- reorderLetExprsFunBody definedVars' delayedExprMap rhs
                            pure (dcon, vs, rhs')) ls
            pure $ CaseE e' ls'

        TimeIt e _t b -> do
            e' <- reorderLetExprsFunBody definedVars delayedExprMap e
            pure $ TimeIt e' _t b

        SpawnE f lvs ls -> do 
            ls' <- mapM (reorderLetExprsFunBody definedVars delayedExprMap) ls
            pure $ SpawnE f lvs ls'
        
        SyncE -> pure SyncE

        WithArenaE v e -> do
            e' <- reorderLetExprsFunBody definedVars delayedExprMap e
            pure $ WithArenaE v e' 

        MapE _ _ -> error "reorderLetExprsFunBody: MapE not supported!"


        FoldE _ _ _ -> error "reorderLetExprsFunBody: FoldE not supported!"

        WithArenaE v e -> do
            e' <- reorderLetExprsFunBody definedVars delayedExprMap e
            pure $ WithArenaE v e'

        Ext (LetLocE loc rhs bod) -> do
            let freeVarsRhs = gFreeVars rhs
                freeVarsRhs' = S.map (fromVarToFreeVarsTy) freeVarsRhs
                {- Check if variables in rhs are defined -}
                isDefined = S.isSubsetOf freeVarsRhs' definedVars
              in if isDefined
                 then do
                    let definedVars' = S.insert (fromLocVarToFreeVarsTy loc) definedVars
                    bod' <- reorderLetExprsFunBody definedVars' delayedExprMap bod
                    pure $ Ext $ LetLocE loc rhs bod'
                 else do
                    let delayedLetLocE = LetLocExpr loc rhs
                        delayedExprMap' = M.insert freeVarsRhs' delayedLetLocE delayedExprMap
                    bod' <- reorderLetExprsFunBody definedVars delayedExprMap' bod
                    pure bod'

        Ext (StartOfPkdCursor cur) -> pure ex

        Ext (TagCursor a _b) -> pure ex 

        Ext (FromEndE{}) -> pure ex

        Ext (AddFixed{}) -> pure ex

        Ext (RetE _ls v) -> pure ex

        Ext (BoundsCheck{}) -> pure ex

        Ext (IndirectionE tycon _ (a, _) _ _) -> pure ex 

        Ext GetCilkWorkerNum -> pure ex

        Ext (LetAvail _ bod) -> pure ex

        Ext (AllocateTagHere{}) -> pure ex

        Ext (AllocateScalarsHere{}) -> pure ex

        Ext (SSPush{}) -> pure ex

        Ext (SSPop{}) -> pure ex

        Ext (LetRegionE r sz ty bod) -> do
            bod' <- reorderLetExprsFunBody definedVars delayedExprMap bod
            pure $ Ext $ LetRegionE r sz ty bod'
        
        _ -> error $ "reorderLetExprs : unexpected expression not handled!!" ++ sdoc ex
        _ -> pure ex

