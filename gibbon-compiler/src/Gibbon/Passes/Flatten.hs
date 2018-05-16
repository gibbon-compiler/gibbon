{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}


-- | Put the program in A-normal form where only varrefs and literals are
-- allowed in operand position.
--
--- GRAMMAR: takes an L1 program and returns an L1 program in
--- restricted form.

module Gibbon.Passes.Flatten
    ( flattenL1, flattenL2, flattenL3 ) where

import Control.Monad.State
import Data.Loc
import Text.PrettyPrint.GenericPretty
import Prelude hiding (exp)
import qualified Data.Map as M

import Gibbon.Common
import Gibbon.GenericOps
import Gibbon.L1.Syntax as L1
import qualified Gibbon.L2.Syntax as L2
import qualified Gibbon.L3.Syntax as L3


-- | Flatten ensures that function operands are "trivial".
--
--   In the process, it also lifts lets out of case scrutinees, if
--   conditions, and tuple operands.
--
--   Note that it does not require tail expressions to be trivial.
--   For example, it allows AppE and PrimAppE in the body of a
--   let-expression.
flattenL1 :: L1.Prog -> SyM L1.Prog
flattenL1 prg@(L1.Prog defs funs main) = do
    main' <- case main of
               Just (e,ty) -> Just <$> (,ty) <$> gFlattenExp defs env20 e
               Nothing -> return Nothing
    funs' <- flattenFuns funs
    return $ L1.Prog defs funs' main'
  where
    flattenFuns = mapM flattenFun
    flattenFun (FunDef nam narg (targ, ty) bod) = do
      let env2 = Env2 (M.singleton narg targ) (fEnv env20)
      bod' <- gFlattenExp defs env2 bod
      return $ FunDef nam narg (targ, ty) bod'

    env20 = L1.progToEnv prg

flattenL2 :: Flattenable (L2.E2Ext Var (UrTy LocVar)) => L2.Prog -> SyM L2.Prog
flattenL2 prg@(L2.Prog defs funs main) = do
    main' <-
      case main of
        Nothing -> return Nothing
        Just (ex,ty) -> fmap (Just . (,ty)) (gFlattenExp defs env20 ex)
    funs' <- flattenFuns funs
    return $ L2.Prog defs funs' main'
  where
    flattenFuns = mapM flattenFun
    flattenFun (L2.FunDef nam narg ty bod) = do
      let env2 = Env2 (M.singleton narg (L2.arrIn ty)) (fEnv env20)
      bod' <- gFlattenExp defs env2 bod
      return $ L2.FunDef nam narg ty bod'

    env20 = L2.progToEnv prg


flattenL3 :: L3.Prog -> SyM L3.Prog
flattenL3 prg@(L3.Prog defs funs main) = do
    main' <-
      case main of
        Nothing -> return Nothing
        Just (ex,ty) -> fmap (Just . (,ty)) (gFlattenExp defs env20 ex)
    funs' <- flattenFuns funs
    return $ L3.Prog defs funs' main'
  where
    flattenFuns = mapM flattenFun
    flattenFun (L3.FunDef nam narg ty bod) = do
      let env2 = Env2 (M.singleton narg (L3.arrIn ty)) (fEnv env20)
      bod' <- gFlattenExp defs env2 bod
      return $ L3.FunDef nam narg ty bod'

    env20 = L3.progToEnv prg


-- NOTE: / FIXME
-- If we would just include arrow types in the grammar from the start,
-- the the typeenv could contain function types too.  Data constructors could
-- go in there too.  Everything would be simpler. We would simply have to
-- use other means to remember that L1 programs are first order.

type Exp e l = PreExp e l (UrTy l)

type Binds e = (Var,[LocOf e],TyOf e, e)


instance (Show l, Out l, Expression (e l (UrTy l)),
          TyOf (e l (UrTy l)) ~ TyOf (Exp e l),
          Typeable (e l (UrTy l)),
          Flattenable (e l (UrTy l)))
       => Flattenable (L (Exp e l)) where

  gFlattenGatherBinds = exp

  gFlattenExp ddfs env ex = do (b,e') <- exp ddfs env ex
                               return $ flatLets b e'


exp :: forall l e .
       (Show l, Out l,
       TyOf (e l (UrTy l)) ~ TyOf (Exp e l),
       Typeable (e l (UrTy l)),
       Flattenable (e l (UrTy l)))
    => DDefs (TyOf (L (Exp e l)))
    -> Env2 (TyOf (L (Exp e l)))
    -> L (Exp e l)
    -> SyM ([Binds (L (Exp e l))], L (Exp e l))
exp ddfs env2 (L sloc e0) =
  let triv :: String -> L (Exp e l) -> SyM ([Binds (L (Exp e l))], L (Exp e l))
      triv m e = -- Force something to be trivial
        if isTrivial e
        then return ([],e)
        else do tmp <- gensym $ toVar $ "flt" ++ m
                let ty = gTypeExp ddfs env2 e
                (bnds,e') <- exp ddfs env2 e
                return ( bnds++[(tmp,[],ty,e')]
                       , L NoLoc $ VarE tmp)

      go :: L (Exp e l) -> SyM ([Binds (L (Exp e l))], L (Exp e l))
      go = exp ddfs env2

      gols f ls m = do (bndss,ls') <- unzip <$> mapM (triv m) ls
                       return (concat bndss, f ls')

  in fmap (\(a,b) -> (a, L sloc b)) $
  case e0 of
    Ext ext   -> do (_bnds,e) <- gFlattenGatherBinds ddfs env2 ext
                    return  ([], Ext e)

    LitE _    -> return ([], e0)
    VarE    _ -> return ([],e0)
    LitSymE _ -> return ([],e0)

    AppE f lvs arg    -> do (b1,arg') <- triv "Ap" arg
                            return (b1, AppE f lvs arg')

    PrimAppE p ls     -> gols (PrimAppE p)  ls "Prm"
    MkProdE ls        -> gols  MkProdE      ls "Prd"
    DataConE loc k ls -> gols (DataConE loc k) ls "Pkd"

    LetE (v1,lv1,t1, (L sloc' (LetE (v2,lv2,t2,rhs2) rhs1))) bod -> do
      (bnd, rhs) <- go (L sloc' $
                        LetE (v2,lv2,t2,rhs2) $
                        L sloc' $
                        LetE (v1,lv1,t1,rhs1) bod)
      return (bnd, unLoc rhs)

    LetE (v,locs,t,rhs) bod -> do (bnd1,rhs') <- go rhs
                                  (bnd2,bod') <- exp ddfs (extendVEnv v t env2) bod
                                  return (bnd1++[(v,locs,t,rhs')]++bnd2, unLoc bod')
    IfE a b c -> do (b1,a') <- triv "If" a
                    (b2,b') <- go b
                    (b3,c') <- go c
                    return (b1, IfE a' (flatLets b2 b') (flatLets b3 c'))
    -- This can happen anywhere, but doing it here prevents
    -- unneccessary bloat where we can ill afford it:
    ProjE ix (L _ (MkProdE ls)) -> do
      -- dbgTrace 5 (" [flatten] Reducing project-of-tuple, index "++show ix++
      --             " expr:  "++take 80 (show l)++"...")
      (bnd,rhs) <- go (ls !! ix)
      return (bnd, unLoc rhs)

    ProjE ix e -> do (b,e') <- triv "Prj" e
                     return (b, ProjE ix e')

    CaseE e ls -> do (b,e') <- triv "Cse" e
                     ls' <- forM ls $ \ (k,vrs,rhs) -> do
                              let tys = lookupDataCon ddfs k
                                  vrs' = map fst vrs
                                  env2' = extendsVEnv (M.fromList (zip vrs' tys)) env2
                              (b2,rhs') <- exp ddfs env2' rhs
                              return (k,vrs, flatLets b2 rhs')
                     return (b, CaseE e' ls')
    -- TimeIt is treated like a conditional.  Don't lift out of it:
    TimeIt e _t b -> do
      (bnd,e') <- go e
      return ([], TimeIt (flatLets bnd e') (gTypeExp ddfs env2 e) b)
    MapE _ _      -> error "FINISHLISTS"
    FoldE _ _ _   -> error "FINISHLISTS"
