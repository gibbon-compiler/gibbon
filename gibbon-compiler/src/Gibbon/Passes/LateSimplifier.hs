module Gibbon.Passes.LateSimplifier ( lateInlineTriv ) where

import qualified Data.Map as M
import           Gibbon.Common
import           Gibbon.L4.Syntax

--------------------------------------------------------------------------------

lateInlineTriv :: Prog -> PassM Prog
lateInlineTriv (Prog info_tbl sym_tbl fundefs mainExp) = do
    let fundefs' = map lateInlineTrivFn fundefs
        mainExp' = case mainExp of
                       Just (PrintExp tl) -> do
                           Just (PrintExp (lateInlineTrivExp M.empty tl))
                       Nothing -> Nothing
    return $ Prog info_tbl sym_tbl fundefs' mainExp'
  where
    lateInlineTrivFn :: FunDecl -> FunDecl
    lateInlineTrivFn f@FunDecl{funBody} =
        let bod' = lateInlineTrivExp M.empty funBody
        in f {funBody = bod'}

    lateInlineTrivExp :: M.Map Var Triv -> Tail -> Tail
    lateInlineTrivExp = go
      where
        gotriv env trv =
            case trv of
                VarTriv v -> case M.lookup v env of
                                 Nothing -> trv
                                 Just t2 -> t2
                ProdTriv ls -> ProdTriv (map (gotriv env) ls)
                ProjTriv i t -> ProjTriv i (gotriv env t)
                _ -> trv

        goalts env alts =
            case alts of
                TagAlts ls -> TagAlts $ map (\(t,tl) -> (t,go env tl)) ls
                IntAlts ls -> IntAlts $ map (\(t,tl) -> (t,go env tl)) ls
        go env tl =
              case tl of
                   RetValsT trvs ->
                       RetValsT (map (gotriv env) trvs)
                   AssnValsT upd mb_bod ->
                       AssnValsT upd (fmap (go env) mb_bod)
                   LetCallT async binds rator rands bod ->
                       LetCallT async binds rator (map (gotriv env) rands) (go env bod)
                   LetPrimCallT binds prim rands bod ->
                       LetPrimCallT binds prim (map (gotriv env) rands) (go env bod)
                   LetTrivT (v,_ty,trv) bod ->
                       case trv of
                           VarTriv w -> case M.lookup w env of
                                            Nothing -> go (M.insert v trv env) bod
                                            Just trv' -> go (M.insert v trv' env) bod
                           _ -> go (M.insert v (gotriv env trv) env) bod
                   LetIfT binds (trv,tl1,tl2) bod ->
                       LetIfT binds (gotriv env trv, go env tl1, go env tl2) (go env bod)
                   LetUnpackT binds ptr bod ->
                       LetUnpackT binds ptr (go env bod)
                   LetAllocT lhs vals bod ->
                       LetAllocT lhs (map (\(ty,trv) -> (ty,gotriv env trv)) vals) (go env bod)
                   LetAvailT vars bod ->
                       LetAvailT vars (go env bod)
                   IfT tst thn els ->
                       IfT (gotriv env tst) (go env thn) (go env els)
                   ErrT str -> ErrT str
                   LetTimedT isiter binds timed bod ->
                       LetTimedT isiter binds (go env timed) (go env bod)
                   Switch lbl trv alts mb_tl ->
                       Switch lbl trv (goalts env alts) (fmap (go env) mb_tl)
                   TailCall var trvs ->
                       TailCall var (map (gotriv env) trvs)
                   Goto lbl -> Goto lbl
                   LetArenaT lhs bod ->
                       LetArenaT lhs (go env bod)
