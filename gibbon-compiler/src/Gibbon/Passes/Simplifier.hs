{-# LANGUAGE FlexibleContexts #-}

module Gibbon.Passes.Simplifier ( simplifyL1, lateInlineTriv ) where

import Data.Functor.Foldable as Foldable
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List ( isPrefixOf )

import Gibbon.Common
import Gibbon.Language
import Gibbon.L1.Syntax
import qualified Gibbon.L4.Syntax as L4
import Gibbon.Passes.Freshen (freshNames1, freshFun1)

--------------------------------------------------------------------------------

markRecFns :: Prog1 -> PassM Prog1
markRecFns (Prog ddefs fundefs main) = do
    let fundefs' = M.map
                     (\fn@FunDef{funName,funBody} ->
                          if funName `S.member` (gFreeVars funBody)
                          then fn { funRec = Rec }
                          else fn)
                     fundefs
    pure (Prog ddefs fundefs' main)

inlineFuns :: Prog1 -> PassM Prog1
inlineFuns (Prog ddefs fundefs main) = do
    main' <- case main of
               Nothing -> pure Nothing
               Just (e,ty) -> do
                 e' <- (cataM go) e
                 pure $ Just (e', ty)
    fundefs' <- mapM (\fn -> do
                           bod <- (cataM go) (funBody fn)
                           pure $ fn { funBody = bod})
                     fundefs
    pure (Prog ddefs fundefs' main')
  where
    go :: PreExpF E1Ext () (UrTy ()) Exp1 -> PassM Exp1
    go ex =
      case ex of
        AppEF f [] args -> do
            let fn = fundefs M.! f
            if funInline fn == Inline && funRec fn == NotRec
              then do
                FunDef{funArgs,funTy,funBody} <- freshFun1 fn
                let in_tys = fst funTy
                    binds = map (\(v,ty,e) -> (v,[],ty,e)) (zip3 funArgs in_tys args)
                pure $ mkLets binds funBody
              else do
                args' <- mapM (go . project) args
                pure $ AppE f [] args'
        _ -> pure $ embed ex

deadFunElim :: Prog1 -> PassM Prog1
deadFunElim (Prog ddefs fundefs main) = do
    let used = case main of
                 Nothing -> S.empty
                 Just (e,_) -> gFreeVars e
    let used' = getUsedFns used S.empty used
    let (fundefs',deleted) =
            M.foldr (\fn (acc1,acc2) ->
                         let f = funName fn in
                           if f `S.member` used' || isPrefixOf "_" (fromVar f)
                           then (M.insert f fn acc1, acc2)
                           else (acc1, f:acc2))
                    (M.empty,[])
                    fundefs
    dbgTrace 3 ("Removed unused functions: " ++ show deleted) $
      pure (Prog ddefs fundefs' main)
  where
    getUsedFns :: S.Set Var -> S.Set Var -> S.Set Var -> S.Set Var
    getUsedFns todo inspected acc =
      if S.null todo
      then acc
      else
        let f = S.elemAt 0 todo
            todo' = S.deleteAt 0 todo
        in if f `S.member` inspected
           then getUsedFns todo' inspected acc
           else
             let FunDef{funArgs, funName,funBody} = fundefs M.! f
                 free = (gFreeVars funBody) `S.difference` (S.fromList (funName : funArgs))
             in getUsedFns (free <> todo') (S.insert f inspected) (acc <> free)

simplifyL1 :: Prog1 -> PassM Prog1
simplifyL1 p0 = do
    p0' <- freshNames1 p0
    p1 <- markRecFns p0'
    p2 <- inlineFuns p1
    p3 <- deadFunElim p2
    pure p3


--------------------------------------------------------------------------------

lateInlineTriv :: L4.Prog -> PassM L4.Prog
lateInlineTriv (L4.Prog info_tbl sym_tbl fundefs mainExp) = do
    let fundefs' = map lateInlineTrivFn fundefs
        mainExp' = case mainExp of
                       Just (L4.PrintExp tl) -> do
                           Just (L4.PrintExp (lateInlineTrivExp M.empty tl))
                       Nothing -> Nothing
    return $ L4.Prog info_tbl sym_tbl fundefs' mainExp'
  where
    lateInlineTrivFn :: L4.FunDecl -> L4.FunDecl
    lateInlineTrivFn f@L4.FunDecl{L4.funBody} =
        let bod' = lateInlineTrivExp M.empty funBody
        in f {L4.funBody = bod'}

    lateInlineTrivExp :: M.Map Var L4.Triv -> L4.Tail -> L4.Tail
    lateInlineTrivExp = go
      where
        gotriv env trv =
            case trv of
                L4.VarTriv v -> case M.lookup v env of
                                 Nothing -> trv
                                 Just t2 -> t2
                L4.ProdTriv ls -> L4.ProdTriv (map (gotriv env) ls)
                L4.ProjTriv i t -> L4.ProjTriv i (gotriv env t)
                _ -> trv

        goalts env alts =
            case alts of
                L4.TagAlts ls -> L4.TagAlts $ map (\(t,tl) -> (t,go env tl)) ls
                L4.IntAlts ls -> L4.IntAlts $ map (\(t,tl) -> (t,go env tl)) ls
        go env tl =
              case tl of
                   L4.RetValsT trvs ->
                       L4.RetValsT (map (gotriv env) trvs)
                   L4.AssnValsT upd mb_bod ->
                       L4.AssnValsT upd (fmap (go env) mb_bod)
                   L4.LetCallT async binds rator rands bod ->
                       L4.LetCallT async binds rator (map (gotriv env) rands) (go env bod)
                   L4.LetPrimCallT binds prim rands bod ->
                       L4.LetPrimCallT binds prim (map (gotriv env) rands) (go env bod)
                   L4.LetTrivT (v,_ty,trv) bod ->
                       case trv of
                           L4.VarTriv w -> case M.lookup w env of
                                            Nothing -> go (M.insert v trv env) bod
                                            Just trv' -> go (M.insert v trv' env) bod
                           _ -> go (M.insert v (gotriv env trv) env) bod
                   L4.LetIfT binds (trv,tl1,tl2) bod ->
                       L4.LetIfT binds (gotriv env trv, go env tl1, go env tl2) (go env bod)
                   L4.LetUnpackT binds ptr bod ->
                       L4.LetUnpackT binds ptr (go env bod)
                   L4.LetAllocT lhs vals bod ->
                       L4.LetAllocT lhs (map (\(ty,trv) -> (ty,gotriv env trv)) vals) (go env bod)
                   L4.LetAvailT vars bod ->
                       L4.LetAvailT vars (go env bod)
                   L4.IfT tst thn els ->
                       L4.IfT (gotriv env tst) (go env thn) (go env els)
                   L4.ErrT str -> L4.ErrT str
                   L4.LetTimedT isiter binds timed bod ->
                       L4.LetTimedT isiter binds (go env timed) (go env bod)
                   L4.Switch lbl trv alts mb_tl ->
                       L4.Switch lbl trv (goalts env alts) (fmap (go env) mb_tl)
                   L4.TailCall var trvs ->
                       L4.TailCall var (map (gotriv env) trvs)
                   L4.Goto lbl -> L4.Goto lbl
                   L4.LetArenaT lhs bod ->
                       L4.LetArenaT lhs (go env bod)
