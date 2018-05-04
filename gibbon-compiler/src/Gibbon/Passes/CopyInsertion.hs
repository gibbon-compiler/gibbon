module Gibbon.Passes.CopyInsertion
  ( addCopies, genCopyFn
  ) where

-- | standard library
import Data.Foldable
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad

-- | gibbon internals
import Gibbon.Common
import Gibbon.L2.Syntax as L2
import qualified Gibbon.L1.Syntax as L1

-- | Chatter level for this module:
lvl :: Int
lvl = 4

-- | Naive copy insertion pass
-- General strategy: track function arguments and case bindings, and find which ones appear
-- in tail position, then insert calls to copy functions in their place.
addCopies :: L1.Prog -> SyM L1.Prog
addCopies (L1.Prog dd fundefs mainExp) =
    do mainExp' <- case mainExp of
                     Just m -> do m' <- go m
                                  return $ Just m'
                     Nothing -> return $ Nothing
       fundefs' <- forM fundefs $ \(L1.FunDef nm (arg,inT) outT bod) -> do
                                  if L1.hasPacked inT
                                  then case inT of
                                         ProdTy tys -> do
                                                  let locs = filter (\(ty',_) -> isPacked ty') (zip tys [0..])
                                                  newbod <- foldrM (\(ty',l) acc -> do
                                                                      let tls = exprTails bod
                                                                      if (ProjE l (VarE arg)) `S.member` tls
                                                                      then do
                                                                        let dcon = tyToDataCon ty'
                                                                        arg' <- gensym arg
                                                                        dbgTrace lvl ("\n[addCopies] (prod) subst " ++ (show (ProjE l (VarE arg)))) $ return ()
                                                                        bod' <- go $ substTail (ProjE l (VarE arg)) (VarE arg') acc
                                                                        return $ LetE (arg', ty',
                                                                                       AppE (mkCopyName $ toVar dcon)
                                                                                                (ProjE l (VarE arg))) bod'
                                                                      else return acc)
                                                                        bod locs
                                                  return $ L1.FunDef nm (arg,inT) outT newbod
                                         PackedTy dcon r -> do
                                                  let tls = exprTails bod
                                                  if (VarE arg) `S.member` tls
                                                  then do
                                                    arg' <- gensym arg
                                                    dbgTrace lvl ("\n[addCopies] (packed) subst " ++ (show (VarE arg))) $ return ()
                                                    bod' <- go $ substTail (VarE arg) (VarE arg') bod
                                                    dbgTrace lvl ("\n[addCopies] before subst " ++ (show bod)) $ return ()
                                                    dbgTrace lvl ("\n[addCopies] after subst " ++ (show bod')) $ return ()
                                                    let bod'' = LetE (arg', PackedTy dcon r,
                                                                      AppE (mkCopyName $ toVar dcon) (VarE arg)) bod'
                                                    return $ L1.FunDef nm (arg,inT) outT bod''
                                                  else return $ L1.FunDef nm (arg,inT) outT bod
                                         oth -> error $ "addCopies: handle " ++ show oth
                                  else do bod' <- go bod
                                          return $ L1.FunDef nm (arg,inT) outT bod'
       copyfuns <- mapM genCopyFn (M.elems dd)
       return $ L1.Prog dd (fundefs' `M.union` (M.fromList copyfuns)) mainExp'

    where go ex =
              dbgTrace lvl ("\n[addCopies] go " ++ (show ex)) $
              case ex of
                LetE (v,t,e1) e2 -> do e2' <- go e2
                                       return $ LetE (v,t,e1) e2'
                VarE v -> return $ VarE v
                LitE n -> return $ LitE n
                LitSymE n -> return $ LitSymE n
                AppE v e -> return $ AppE v e
                PrimAppE p ls -> return $ PrimAppE p ls
                ProjE i e -> return $ ProjE i e
                CaseE ce ls -> do ls' <- forM ls $ \(k,vs,bod) -> do
                                           let tls = exprTails bod
                                           let vts = zip vs $ lookupDataCon dd k
                                           bod' <- foldrM (\(v,ty) acc -> do
                                                             if isPacked ty && (VarE v) `S.member` tls
                                                             then do let (PackedTy dcon _r) = ty
                                                                     v' <- gensym v
                                                                     dbgTrace lvl ("\n[addCopies] (case) subst " ++ (show v)) $ return ()
                                                                     acc' <- go $ substTail (VarE v) (VarE v') acc
                                                                     return $ LetE (v', ty, AppE (mkCopyName $ toVar dcon) (VarE v)) acc'
                                                             else return acc)
                                                   bod vts
                                           return (k,vs,bod')
                                  return $ CaseE ce ls'
                MkProdE ls -> return $ MkProdE ls
                DataConE k ls -> return $ DataConE k ls
                TimeIt e t b -> do e' <- go e
                                   return $ TimeIt e' t b
                IfE a b c -> do b' <- go b
                                c' <- go c
                                return $ IfE a b' c'
                MapE _ _ -> error "addCopies.go: FINISHME MapE"
                FoldE _ _ _ -> error "addCopies.go: FINISHME FoldE"


-- | Generate a copy function for a data definition
genCopyFn :: DDef L1.Ty -> SyM (Var, L1.FunDef L1.Ty Exp)
genCopyFn DDef{tyName, dataCons} = do
  arg <- gensym $ toVar "arg"
  casebod <- mapM (\(dcon, tys) -> do
                      xs <- mapM (\_ -> gensym (toVar "x")) tys
                      ys <- mapM (\_ -> gensym (toVar "y")) tys
                      let ys' = map VarE ys
                          exp' = foldr (\(ty,x,y) acc ->
                                        if isPacked ty
                                        then LetE (y,ty,AppE (mkCopyName $ toVar $ tyToDataCon ty) (VarE x)) acc
                                        else LetE (y,ty,VarE x) acc)
                                (L1.DataConE dcon ys')
                                (zip3 tys xs ys)
                      return (dcon, xs, exp'))
             dataCons
  return (mkCopyName tyName,
          L1.FunDef { funName = mkCopyName tyName
                    , funArg = (arg, L1.PackedTy (fromVar tyName) ())
                    , funRetTy = L1.PackedTy (fromVar tyName) ()
                    , funBody = L1.CaseE (L1.VarE arg) casebod
                    })

-- | Find the variable and projection nodes in tail position
exprTails :: Exp -> S.Set Exp
exprTails e =
    case e of
      VarE v -> S.singleton $ VarE v
      LitE _i -> S.empty
      LitSymE _v -> S.empty
      AppE _v _e' -> S.empty
      PrimAppE _ _ -> S.empty
      LetE (v,_,_e2) e1 ->
          let tls = exprTails e1
          in S.delete (VarE v) tls
      CaseE _e ls -> foldr f S.empty ls
          where f (_c,_vs,er) a = exprTails er `S.union` a
      IfE _ e1 e2 -> exprTails e1 `S.union` exprTails e2
      ProjE i e' -> S.singleton $ ProjE i e'
      MkProdE es -> S.unions $ map S.singleton es
      DataConE _k _ls -> S.empty
      TimeIt e' _t _b -> exprTails e'

-- | Expression substitution, but only for tail position and only in certain situations.
-- This is meant for when we need to insert a reference to a copy.
substTail :: Exp -> Exp -> Exp -> Exp
substTail old new ex =
  let go = substTail old new in
  case ex of
    VarE v | (VarE v) == old  -> new
           | otherwise -> VarE v
    LitE _          -> ex
    LitSymE _       -> ex
    AppE _ _        -> ex
    PrimAppE _ _    -> ex
    LetE (v,t,rhs) bod | (VarE v) == old -> LetE (v,t,rhs) bod
                       | otherwise -> LetE (v,t,rhs) (go bod)
    ProjE i e  | ProjE i e == old -> new
               | otherwise -> ProjE i e
    CaseE e ls -> CaseE e (map f ls)
        where f (c,vs,er) = if old `elem` (map VarE vs)
                            then (c,vs,er)
                            else (c,vs,go er)
    MkProdE ls     -> MkProdE $ map go ls
    DataConE _ _  -> ex
    TimeIt e t b -> TimeIt (go e) t b
    IfE a b c -> IfE a (go b) (go c)
    MapE _ _ -> error "substTail: FINISHME MapE"
    FoldE _ _ _ -> error "substTail: FINISHME FoldE"


-- |
mkCopyName :: Var -> Var
mkCopyName v = varAppend (toVar "copy") v

-- |
isPacked :: L1.Ty -> Bool
isPacked PackedTy{} = True
isPacked _ = False

-- |
tyToDataCon :: L1.Ty -> DataCon
tyToDataCon (PackedTy dcon _) = dcon
tyToDataCon oth = error $ "tyToDataCon: " ++ show oth ++ " is not packed"
