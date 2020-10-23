{-# LANGUAGE FlexibleContexts #-}

module Gibbon.Passes.Simplifier where

import Data.Functor.Foldable as Foldable
import qualified Data.Set as S
import qualified Data.Map as M

import Gibbon.Common
import Gibbon.Language
import Gibbon.L1.Syntax
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
                           if f `S.member` used'
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

simplify :: Prog1 -> PassM Prog1
simplify p0 = do
    p0' <- freshNames1 p0
    p1 <- markRecFns p0'
    p2 <- inlineFuns p1
    -- p3 <- deadFunElim p2
    pure p2
