-- | Unique names.

module Gibbon.Passes.Freshen (freshNames) where

import Control.Exception
import Data.Loc
import Prelude hiding (exp)
import qualified Data.Map as M
import qualified Data.List as L

import Gibbon.Common
import Gibbon.L1.Syntax


-- FIXME: Naughty to use lists as maps.  Use something with O(N)
-- lookup.  We should standardize on a fast symbol-map.

-- | Rename all local variables.
freshNames :: Prog1 -> PassM Prog1
freshNames (Prog defs funs main) =
    do main' <- case main of
                  Nothing -> return Nothing
                  Just (m,ty) -> do m' <- freshExp [] m
                                    return $ Just (m',ty)
       funs' <- freshFuns funs
       return $ Prog defs funs' main'
    where freshFuns m = M.fromList <$> mapM freshFun (M.toList m)
          freshFun (nam, FunDef _ narg (targ,ty) bod) =
              do narg' <- gensym narg
                 bod' <- freshExp [(narg,narg')] bod
                 let nam' = cleanFunName nam
                 return (nam', FunDef nam' narg' (targ,ty) bod')

          freshExp :: [(Var,Var)] -> L Exp1 -> PassM (L Exp1)
          freshExp vs (L sloc exp) = fmap (L sloc) $
            case exp of
              Ext _     -> return exp
              LitE i    -> return $ LitE i
              LitSymE v -> return $ LitSymE v

              VarE v ->
                case lookup v vs of
                  Nothing -> return $ VarE v
                  Just v' -> return $ VarE v'

              AppE v ls e -> assert ([] == ls) $ do
                e' <- freshExp vs e
                return $ AppE (cleanFunName v) [] e'

              PrimAppE p es -> do
                es' <- mapM (freshExp vs) es
                return $ PrimAppE p es'

              LetE (v,ls,t, e1) e2 -> assert ([]==ls) $ do
                e1' <- freshExp vs e1
                v'  <- gensym v
                e2' <- freshExp ((v,v'):vs) e2
                return $ LetE (v',[],t,e1') e2'

              IfE e1 e2 e3 -> do
                e1' <- freshExp vs e1
                e2' <- freshExp vs e2
                e3' <- freshExp vs e3
                return $ IfE e1' e2' e3'

              ProjE i e -> do
                e' <- freshExp vs e
                return $ ProjE i e'

              MkProdE es -> do
                es' <- mapM (freshExp vs) es
                return $ MkProdE es'

              CaseE e mp -> do
                e' <- freshExp vs e
                -- Here we freshen locations:
                mp' <- mapM (\(c,prs,ae) ->
                             let (args,_) = unzip prs in
                             do
                               args' <- mapM gensym args
                               let vs' = (zip args args') ++ vs
                               ae' <- freshExp vs' ae
                               return (c, L.map (,()) args', ae')) mp
                return $ CaseE e' mp'

              DataConE () c es -> do
                es' <- mapM (freshExp vs) es
                return $ DataConE () c es'

              TimeIt e t b -> do
                e' <- freshExp vs e
                return $ TimeIt e' t b

              ParE a b -> do
                ParE <$> freshExp vs a <*> freshExp vs b

              MapE (v,t,b) e -> do
                b' <- freshExp vs b
                e' <- freshExp vs e
                return $ MapE (v,t,b') e'

              FoldE (v1,t1,e1) (v2,t2,e2) e3 -> do
                e1' <- freshExp vs e1
                e2' <- freshExp vs e2
                e3' <- freshExp vs e3
                return $ FoldE (v1,t1,e1') (v2,t2,e2') e3'