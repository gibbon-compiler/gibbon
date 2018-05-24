-- UNFINISHED?

module Gibbon.L0.Mono
  ()
  where

import Data.Map as M
import Data.List as L
import Data.Loc
import Control.Monad.State

import Gibbon.Common as C
-- import Gibbon.GenericOps

import Gibbon.L0.Syntax as L0
import Gibbon.L1.Syntax as L1

-- | specializing functions on types
type Exp = (L Exp0)

-- | polymorphic/monomorphic functions
type PolyFD = PFDef Ty0 Exp
type MonoFD = FunDef0

-- | polymorphic/monomorphic variable defns
type PolyVD = PVDef Ty0 Exp
type MonoVD = VarDef Ty0 Exp

-- | polymorphic/monomorphic data defns
type PolyDD = PDDef Ty0
type MonoDD = DDef Ty0


data Defn = VDef MonoVD
          | FDef MonoFD
          | Def  MonoDD

type Defns = Map Var Defn

isPolyFun :: PolyFD -> Either PolyFD MonoFD
isPolyFun (PFDef name arg (ForAll [] (ArrowTy t0 t1)) b) =
  Right $ FunDef name arg (t0,t1) b
isPolyFun pf = Left pf


isPolyVar :: PolyVD -> Either PolyVD MonoVD
isPolyVar (PVDef n (ForAll [] t) b) =
  Right $ VarDef n t b
isPolyVar pf = Left pf

isPolyDef :: PolyDD -> Either PolyDD MonoDD
isPolyDef pd@(PDDef n ds) =
  if allMono then Right $ DDef n mds else Left pd
   where mds = filterAndMono ds
         allMono = L.length ds == L.length mds

filterAndMono :: [(DataCon,[(IsBoxed,Scheme Ty0)])] -> [(DataCon,[(IsBoxed,Ty0)])]
filterAndMono ds =
  L.foldr mono [] $ L.filter isMono ds
  where mono = (\ d acc ->
                  case d of
                    (c,s) -> ((c,s'):acc)
                      where s' = L.map (\(i, ForAll _ t) -> (i,t)) s)
        isMono = (\ d -> case d of
                          (_, s) -> L.foldr emptyTyScheme True s)
        emptyTyScheme = (\ (_, ForAll vs _) acc -> if vs == [] then acc else False)

filterPDefs :: PDDefs Ty0 -> (PDDefs Ty0, DDefs Ty0)
filterPDefs pds = M.foldr (\ pd (acc1,acc2) ->
                             case isPolyDef pd of
                               Left  y -> (M.insert (dName y) y acc1, acc2)
                               Right n -> (acc1, M.insert (tyName n) n acc2))
                  (M.empty, M.empty)
                  pds

filterPFDefs :: PFDefs Ty0 Exp -> (PFDefs Ty0 Exp, FunDefs0)
filterPFDefs pfds = M.foldr (\ pd (acc1,acc2) ->
                             case isPolyFun pd of
                               Left  y -> (M.insert (fName y) y acc1,acc2)
                               Right n -> (acc1, M.insert (funName n) n acc2))
                  (M.empty, M.empty)
                  pfds

filterPVDefs :: PVDefs Ty0 Exp -> (PVDefs Ty0 Exp, VarDefs Ty0 Exp)
filterPVDefs pfds = M.foldr (\ pv (acc1,acc2) ->
                             case isPolyVar pv of
                               Left  y -> (M.insert (vName y) y acc1,acc2)
                               Right n -> (acc1, M.insert (varName n) n acc2))
                  (M.empty, M.empty)
                  pfds

updatePF :: PolyFD -> (Ty0 , Ty0) -> MonoFD
updatePF (PFDef name arg _ b)  (t0, t1) =
  let newName = addToName name t0 in
  FunDef newName arg (t0,t1) $ replaceName name newName b

updatePV :: PolyVD -> Ty0 -> MonoVD
updatePV (PVDef name _ b) t =
  let newName = addToName name t in
  VarDef newName t $ replaceName name newName b

updatePD :: PolyDD -> [(DataCon, [(IsBoxed,Ty0)])] -> MonoDD
updatePD (PDDef name _) ts =
  DDef (addToName name $ L.map snd ts) ts


traverseAndCopy :: PProg -> MProg
traverseAndCopy (PProg ds fs vs main) =
  MProg ddefs fdefs vdefs main'
  where (pds, mds) = filterPDefs ds
        (pfs, _)   = filterPFDefs fs
        (pvs, _)   = filterPVDefs vs

        (lfs, defns1)  = runState (mapM (tACFunDef pfs pvs pds . snd) (M.toList fs)) M.empty
        fds = M.fromList $ L.map (\ f -> ((fName f) , f)) lfs
        (pfs', mfs) = filterPFDefs fds
        (lvs, defns2)  = runState (mapM (tACVarDef pfs' pvs pds . snd) (M.toList vs)) defns1
        vds = M.fromList $ L.map (\ v -> ((vName v) , v)) lvs
        (pvs', mvs) = filterPVDefs vds
        (main', defns) =
          case main of
            Just p  -> let (p',ds') = runState (tACExp pfs' pvs' pds p) defns2 in
                         (Just p', ds')
            Nothing -> (Nothing, defns2)
        (ddefs, fdefs, vdefs) = mergeDefns defns mds mfs mvs


tACFunDef :: PFDefs Ty0 Exp -> PVDefs Ty0 Exp -> PDDefs Ty0 -> PolyFD -> State Defns PolyFD
tACFunDef pfs pvs pds PFDef{fName,fArg,fTy,fBody} =
 PFDef fName fArg fTy <$> tACExp pfs pvs pds fBody

tACVarDef :: PFDefs Ty0 Exp -> PVDefs Ty0 Exp -> PDDefs Ty0 -> PolyVD -> State Defns PolyVD
tACVarDef pfs pvs pds PVDef{vName,vTy,vBody} =
 PVDef vName vTy <$> tACExp pfs pvs pds vBody

tACExp :: PFDefs Ty0 Exp -> PVDefs Ty0 Exp -> PDDefs Ty0 -> Exp -> State Defns Exp
tACExp pfs pvs pds (L loc e) = L loc <$>
  case e of
    -- ^ functions
    AppE f ls a -> case M.lookup f pfs of
                     Just fd -> do
                       a' <- go a
                       let t = getFDType -- ^ TODO get types
                           nfd = updatePF fd t
                           fdName = funName nfd
                       ds' <- get
                       _   <- put $ M.insert fdName (FDef nfd) ds'
                       return $ AppE fdName ls a'
                     Nothing -> do
                       a' <- go a
                       return $ AppE f ls a'
    -- ^ calls to variable definitions
    Ext (PolyAppE f d) | isVarE $ funCall f ->
                           case M.lookup (var $ funCall f) pvs of
                             Just vd -> do
                               d' <- go d
                               let ts = getVDType -- ^ TODO get types
                                   nvd = updatePV vd ts
                                   vdName = varName nvd
                               ds' <- get
                               f'  <- updatePolyF f vdName
                               _   <- put $ M.insert vdName (VDef nvd) ds'
                               return $ Ext $ PolyAppE f' d'
                             Nothing -> do
                               d' <- go d
                               f' <- go f
                               return $ Ext $ PolyAppE f' d'
    -- ^ calls to data defns
    DataConE lc dc es -> case M.lookup (toVar dc) pds of
                           Just dd -> do
                             es' <- mapM go es
                             let ts = getDDType -- ^ TODO get types
                                 ndd = updatePD dd ts
                                 ddName = tyName ndd
                             ds' <- get
                             _   <- put $ M.insert ddName (Def ndd) ds'
                             return $ DataConE lc (fromVar ddName) es'
                           Nothing -> do
                             es' <- mapM go es
                             return $ DataConE lc dc es'
    PrimAppE p ls -> PrimAppE p <$> mapM go ls
    MkProdE ls -> MkProdE <$> mapM go ls
    ProjE i x  -> ProjE i <$> go x
    IfE p t f -> IfE <$> go p <*> go t <*> go f
    CaseE k ls -> CaseE <$> go k <*> mapM f ls
      where f = \ (dc,v,ex) -> (dc,v,) <$> go ex
    LetE (v,lc,ty,rhs) b -> LetE <$> (v,lc,ty,) <$> go rhs <*> go b
    TimeIt x t b -> do
      x' <- go x
      return $ TimeIt x' t b
    Ext ext ->
      case ext of
        PolyAppE f d -> do
          f' <- go f
          d' <- go d
          return $ Ext $ PolyAppE f' d'
        LambdaE x b  -> Ext <$> LambdaE x <$> go b
    _ -> return e
  where go = tACExp pfs pvs pds
        updatePolyF :: Exp -> Var -> State Defns Exp
        updatePolyF (L loc' e') v = L loc' <$>
          case e' of
            VarE _ -> return $ VarE v
            Ext (PolyAppE f d) -> do
              d' <- go d
              f' <- updatePolyF f v
              return $ Ext (PolyAppE f' d')
            err -> return $ err

-- Helpers

mergeDefns :: Defns -> DDefs Ty0 -> FunDefs0 -> VarDefs Ty0 Exp -> (DDefs Ty0, FunDefs0, VarDefs Ty0 Exp)
mergeDefns defns ds fs vs = (M.union dds ds, M.union dfs fs, M.union dvs vs)
  where (dds, dfs, dvs) = L.foldr f (M.empty, M.empty, M.empty) $ M.toList defns
        f (v,defn) (dds', dfs', dvs') =
          case defn of
            VDef vd -> (dds', dfs', M.insert v vd dvs')
            FDef fd -> (dds', M.insert v fd dfs', dvs')
            Def dd  -> (M.insert v dd dds', dfs', dvs')

funCall :: Exp -> Exp
funCall (L loc ex) =
  case ex of
    Ext (PolyAppE (L _ (VarE v)) _) -> L loc $ VarE v
    Ext (PolyAppE f _) -> funCall f
    e                  -> L loc $ e

var :: Exp -> Var
var (L _ (VarE v)) = v
var e = error $ "Not a var " ++ show e

isVarE :: Exp -> Bool
isVarE (L _ e) = case e of
                   VarE _ -> True
                   _      -> False

replaceName :: Var -> Var -> Exp -> Exp
replaceName old new (L loc b) = L loc $
  case b of
    VarE v | v == old -> VarE new
    AppE f ls a | f == old -> AppE new ls $ go a
    DataConE lc dc es -> DataConE lc dc $ L.map go es
    PrimAppE p ls -> PrimAppE p $ L.map go ls
    MkProdE ls -> MkProdE $ L.map go ls
    ProjE i x  -> ProjE i $ go x
    IfE p t f -> IfE (go p) (go t) (go f)
    CaseE k ls -> CaseE (go k) $ L.map f ls
      where f = \ (dc,v,ex) -> (dc,v, go ex)
    LetE (v,lc,ty,rhs) bd -> LetE (v,lc,ty,go rhs) $ go bd
    TimeIt x t e -> TimeIt (go x) t e
    Ext ext ->
      case ext of
        PolyAppE f d -> Ext $ PolyAppE (go f) (go d)
        LambdaE x bd -> Ext $ LambdaE x $ go bd
    _ -> b
    where go = replaceName old new

addToName :: (Show a) => Var -> a -> Var
addToName v a = toVar $ fromVar v ++ "_" ++ show a


-- ^ TODO get types
getVDType :: Ty0
getVDType = L0.IntTy

getFDType :: (Ty0, Ty0)
getFDType = (L0.IntTy, L0.IntTy)

getDDType :: [(DataCon, [(IsBoxed,Ty0)])]
getDDType = []
