-- | Unique names.

module Gibbon.Passes.Freshen (freshNames) where

import Control.Exception
import Data.Loc
import Prelude hiding (exp)
import qualified Data.Map as M
import qualified Data.List as L

import Gibbon.Common
import Gibbon.L1.Syntax as L1


-- FIXME: Naughty to use lists as maps.  Use something with O(N)
-- lookup.  We should standardize on a fast symbol-map.

-- | Rename all local variables.
freshNames :: L1.Prog1 -> PassM L1.Prog1
freshNames (L1.Prog defs funs main) =
    do main' <- case main of
                  Nothing -> return Nothing
                  Just (m,ty) -> do m' <- freshExp [] m
                                    return $ Just (m',ty)
       funs' <- freshFuns funs
       return $ L1.Prog defs funs' main'
    where freshFuns m = M.fromList <$> mapM freshFun (M.toList m)
          freshFun (nam, FunDef _ narg (targ,ty) bod) =
              do narg' <- gensym narg
                 bod' <- freshExp [(narg,narg')] bod
                 let nam' = cleanFunName nam
                 return (nam', FunDef nam' narg' (targ,ty) bod')

          freshExp :: [(Var,Var)] -> L Exp1 -> PassM (L L1.Exp1)
          freshExp vs (L sloc exp) = fmap (L sloc) $
            case exp of
              L1.Ext _     -> return exp
              L1.LitE i    -> return $ L1.LitE i
              L1.LitSymE v -> return $ L1.LitSymE v

              L1.VarE v ->
                case lookup v vs of
                  Nothing -> return $ L1.VarE v
                  Just v' -> return $ L1.VarE v'

              L1.AppE v ls e -> assert ([] == ls) $ do
                e' <- freshExp vs e
                return $ L1.AppE (cleanFunName v) [] e'

              L1.PrimAppE p es -> do
                es' <- mapM (freshExp vs) es
                return $ L1.PrimAppE p es'

              L1.LetE (v,ls,t, e1) e2 -> assert ([]==ls) $ do
                e1' <- freshExp vs e1
                v'  <- gensym v
                e2' <- freshExp ((v,v'):vs) e2
                return $ L1.LetE (v',[],t,e1') e2'

              L1.IfE e1 e2 e3 -> do
                e1' <- freshExp vs e1
                e2' <- freshExp vs e2
                e3' <- freshExp vs e3
                return $ L1.IfE e1' e2' e3'

              L1.ProjE i e -> do
                e' <- freshExp vs e
                return $ L1.ProjE i e'

              L1.MkProdE es -> do
                es' <- mapM (freshExp vs) es
                return $ L1.MkProdE es'

              L1.CaseE e mp -> do
                e' <- freshExp vs e
                -- Here we freshen locations:
                mp' <- mapM (\(c,prs,ae) ->
                             let (args,_) = unzip prs in
                             do
                               args' <- mapM gensym args
                               let vs' = (zip args args') ++ vs
                               ae' <- freshExp vs' ae
                               return (c, L.map (,()) args', ae')) mp
                return $ L1.CaseE e' mp'

              L1.DataConE () c es -> do
                es' <- mapM (freshExp vs) es
                return $ L1.DataConE () c es'

              L1.TimeIt e t b -> do
                e' <- freshExp vs e
                return $ L1.TimeIt e' t b

              L1.MapE (v,t,b) e -> do
                b' <- freshExp vs b
                e' <- freshExp vs e
                return $ L1.MapE (v,t,b') e'

              L1.FoldE (v1,t1,e1) (v2,t2,e2) e3 -> do
                e1' <- freshExp vs e1
                e2' <- freshExp vs e2
                e3' <- freshExp vs e3
                return $ L1.FoldE (v1,t1,e1') (v2,t2,e2') e3'
