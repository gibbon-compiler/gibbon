{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Put the program in A-normal form where only varrefs and literals are
-- allowed in operand position.
--
--- GRAMMAR: takes an L1 program and returns an L1 program in
--- restricted form.

module Packed.FirstOrder.Passes.Flatten
    ( flatten
  -- * Some utilities that really should be elsewhere.
  , typeExp, TEnv
  ) where

-------------------------------------------------------------------------------

import Control.Monad.State
import Data.Loc
import Text.PrettyPrint.GenericPretty (Out)

import Packed.FirstOrder.GenericOps
import Packed.FirstOrder.Common
import Packed.FirstOrder.L1.Syntax as L1 hiding (Exp)
import qualified Packed.FirstOrder.L2.Syntax as L2

-- import Packed.FirstOrder.L2.Syntax (isCursorTy)

import qualified Data.Map as M

import Prelude hiding (exp)

-------------------------------------------------------------------------------

-- | Flatten ensures that function operands are "trivial".
--
--   In the process, it also lifts lets out of case scrutinees, if
--   conditions, and tuple operands.
flatten :: L1.Prog -> SyM L1.Prog
flatten prg@(L1.Prog defs funs main) = do
    main' <- mapM (gFlattenExp defs env20) main
    funs' <- flattenFuns funs
    return $ L1.Prog defs funs' main'
  where
    flattenFuns = mapM flattenFun
    -- flattenFun (FunDef nam (narg,targ) ty bod) = do
    flattenFun (FunDef nam narg ty@ArrowTy{arrIn} bod) = do
      let env2 = Env2 (M.singleton narg arrIn) (fEnv env20)
      bod' <- gFlattenExp defs env2 bod
      return $ FunDef nam narg ty bod'

    env20 = L1.progToEnv prg

-- NOTE: / FIXME
-- If we would just include arrow types in the grammar from the start,
-- the the typeenv could contain function types too.  Data constructors could
-- go in there too.  Everything would be simpler. We would simply have to
-- use other means to remember that L1 programs are first order.

type Exp e l   = PreExp e l (UrTy l)

type Binds e l = (Var,[l],UrTy l, L (Exp e l))

type TEnv l    = M.Map Var (UrTy l)

instance Flattenable (PreExp e l d) => Flattenable (L (PreExp e l d)) where
  gFlattenExp defs env (L p ex) = fmap (L p) $ gFlattenExp defs env ex
  -- TODO(cskksc): gFlattenGatherBinds


instance (Out l, Show l, Flattenable (e l (UrTy l)))
         => Flattenable (Exp e l) where
  -- gFlattenGatherBinds :: DDefs (UrTy l) ->
  --                        Env2 (UrTy l) ->
  --                        PreExp e l (UrTy l) ->
  --                        SyM ([Binds e l], PreExp e l (UrTy l))
  -- gFlattenGatherBinds = exp

  gFlattenExp :: DDefs (UrTy l) -> Env2 (UrTy l) -> PreExp e l (UrTy l) ->
                 SyM (Exp e l)
  gFlattenExp ddefs env2 ex0 = do (b,e') <- exp ddefs env2 (L NoLoc ex0)
                                  return $ unLoc $ flatLets b e'


exp :: forall l e . (Show l, Show (e l (UrTy l)), Out l, Out (e l (UrTy l))) =>
       DDefs (UrTy l) -> Env2 (UrTy l) -> L (Exp e l) ->
       SyM ([Binds e l],L (Exp e l))
exp ddefs env2 (L sloc e0) =
     let triv :: String -> L (Exp e l) -> SyM ([Binds e l], L (Exp e l))
         triv m e = -- Force something to be trivial
           if isTriv e
           then return ([],e)
           else do tmp <- gensym $ toVar $ "flt" ++ m
                   let ty = typeExp (ddefs, env2) e
                   (bnds,e') <- exp ddefs env2 e
                   return ( bnds++[(tmp,[],ty,e')]
                          , L NoLoc $ VarE tmp)

         go :: L (Exp e l) -> SyM ([Binds e l], L (Exp e l))
         go = exp ddefs env2

         gols f ls m = do (bndss,ls') <- unzip <$> mapM (triv m) ls
                          return (concat bndss, f ls')

     in fmap (\(a,b) -> (a, L sloc b)) $
     case e0 of
       -- (Ext ext)   -> do (bnds1,e1::e) <- gFlattenGatherBinds ddefs env2 ext
       --                   return ([],Ext e1)
       Ext     _      -> error $ "FINISHME: Flatten:exp Ext"
       VarE    _      -> return ([],e0)
       LitE    _      -> return ([],e0)
       LitSymE _      -> return ([],e0)

       -- This pass is run at multiple points in the compiler pipeline.
       -- We COULD just let these patterns be treated as arbitrary AppE forms,
       -- but it is safer to handle them explicitly.
       L2.AddCursor _ _ -> return ([],e0) -- Already flat.

       L2.NewBuffer     -> return ([],e0) -- Already flat.
       L2.ScopedBuffer  -> return ([],e0) -- Already flat.
       L2.ReadInt _     -> return ([],e0) -- Already flat.
       -- Mimics the AppE case:
       L2.WriteInt v e  -> do (b1,e') <- triv "WI" e; return (b1, L2.WriteInt v e')
       -- A fail-safe:
       _ | L2.isExtendedPattern e0 -> error$ "Unhandled extended L2 pattern: "++ndoc e0

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

       LetE (v,_,t,rhs) bod -> do (bnd1,rhs') <- go rhs
                                  (bnd2,bod') <- exp ddefs (extendVEnv v t env2) bod
                                  return (bnd1++[(v,[],t,rhs')]++bnd2, unLoc bod')

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
                                 let tys = lookupDataCon ddefs k
                                     vrs' = map fst vrs
                                     env2' = extendsVEnv (M.fromList (zip vrs' tys)) env2
                                 (b2,rhs') <- exp ddefs env2' rhs
                                 return (k,vrs, flatLets b2 rhs')
                        return (b, CaseE e' ls')
       -- TimeIt is treated like a conditional.  Don't lift out of it:
       TimeIt e _t b -> do (bnd,e') <- go e
                           return ([], TimeIt (flatLets bnd e') (typeExp (ddefs, env2) e) b)
       MapE _ _      -> error "FINISHLISTS"
       FoldE _ _ _   -> error "FINISHLISTS"


-- | Helper function that lifts out Lets on the RHS of other Lets.
--   Absolutely requires unique names.
mkLetE :: (Var, [l], d, L (PreExp e l d)) -> L (PreExp e l d) -> L (PreExp e l d)
mkLetE (vr,lvs,ty,(L _ (L1.LetE bnd e))) bod = mkLetE bnd $ mkLetE (vr,lvs,ty,e) bod
mkLetE bnd bod = L NoLoc $ L1.LetE bnd bod

-- | Alternative version of L1.mkLets that also flattens
flatLets :: [(Var,[l],d,L (PreExp e l d))] -> L (PreExp e l d) -> L (PreExp e l d)
flatLets [] bod = bod
flatLets (b:bs) bod = mkLetE b (flatLets bs bod)


-- FIXME: Why is this not combined with Typecheck.hs?
-- FIXME: Why does this take an Env2 PLUS a TEnv?

-- | Recover the type of an expression in a type environment.
typeExp :: forall l e . (Show l, Show (e l (UrTy l)), Out l, Out (e l (UrTy l))) =>
           (DDefs (UrTy l), Env2 (UrTy l)) -> L (Exp e l) -> (UrTy l)
typeExp (dd,env2) (L _ exp) =
  case exp of
    L1.LitE _       -> L1.IntTy
    L1.LitSymE _    -> L1.SymTy
    L1.AppE v _ _   -> snd $ fEnv env2 # v
    L1.VarE v       -> M.findWithDefault
                       (error $ "Cannot find type of variable " ++ show v)
                       v (vEnv env2)

    L1.PrimAppE p _ ->
      case p of
        L1.AddP    -> L1.IntTy
        L1.SubP    -> L1.IntTy
        L1.MulP    -> L1.IntTy
        L1.EqIntP  -> L1.BoolTy
        L1.EqSymP  -> L1.BoolTy
        L1.MkTrue  -> L1.BoolTy
        L1.MkFalse -> L1.BoolTy
        L1.Gensym  -> L1.SymTy
        L1.DictInsertP ty -> L1.SymDictTy (noLocsHere ty)
        L1.DictLookupP ty -> noLocsHere ty
        L1.DictEmptyP  ty -> L1.SymDictTy (noLocsHere ty)
        L1.DictHasKeyP ty -> L1.SymDictTy (noLocsHere ty)
        L1.SizeParam      -> L1.IntTy
        L1.ReadPackedFile _ _ ty -> (noLocsHere ty)
        _ -> error $ "case " ++ (show p) ++ " not handled in typeExp yet"

    L1.LetE (v,_,t,_) e -> typeExp (dd,extendVEnv v t env2) e
    L1.IfE _ e _        -> typeExp (dd,env2) e
    L1.MkProdE es       -> L1.ProdTy $ map (typeExp (dd,env2)) es

    L1.DataConE l c _   -> L1.PackedTy (getTyOfDataCon dd c) l
    L1.TimeIt e _ _     -> typeExp (dd,env2) e
    L1.MapE _ e         -> typeExp (dd,env2) e
    L1.FoldE _ _ e      -> typeExp (dd,env2) e
    Ext ex              -> error $ "typeExp: FIXME, internal error. "
                           ++ "Cannot type extension" ++ show ex

    L1.ProjE i e ->
      case typeExp (dd,env2) e of
        (L1.ProdTy tys) -> tys !! i
        oth -> error$ "typeExp: Cannot project fields from this type: "++show oth
               ++"\nExpression:\n  "++ sdoc exp
               ++"\nEnvironment:\n  "++sdoc (vEnv env2)

    L1.CaseE _ mp ->
      let (c,args,e) = head mp
          args' = map fst args
      in typeExp (dd, extendsVEnv
                   (M.fromList (zip args' (lookupDataCon dd c))) env2)
         e


-- This crops up in the types for primitive operations.  Can we remove the need for this?
noLocsHere :: Show a => UrTy a -> UrTy b
noLocsHere t = fmap (\_ -> error $ "This type should not contain a location: "++show t) t
