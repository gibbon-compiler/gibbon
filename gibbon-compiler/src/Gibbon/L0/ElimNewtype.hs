module Gibbon.L0.ElimNewtype where

import Gibbon.L0.Syntax
import Gibbon.Common

import Control.Arrow
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Symbol ( unintern )

elimNewtypes :: Monad m => Prog0 -> m Prog0
elimNewtypes = pure . elimProgram

packedOccurs :: Var -> Ty0 -> Bool
packedOccurs v@(Var s) t = case t of
  PackedTy u ts
    | unintern s == u -> True
    | otherwise -> any go ts
  ProdTy ts -> any go ts
  SymDictTy _ x -> go x
  ArrowTy ts x -> any go ts || go x
  VectorTy x -> go x
  ListTy x -> go x
  _ -> False
  where
    go = packedOccurs v

type TyMap = M.Map String ([Ty0] -> Ty0)
-- type params -> type in terms of params -> args -> substituted type
mkPolyNames :: [TyVar] -> Ty0 -> [Ty0] -> Ty0
mkPolyNames params paramty args =
  substTyVar (M.fromList $ zip params args) paramty

elimProgram :: Prog0 -> Prog0
elimProgram prog =
  Prog
    { mainExp = (elimE connames tynames (ddefs prog) *** elimTy tynames) <$> mainExp prog
    , fundefs = fdefs
    , ddefs = tys
    }
  where
    (newtys, tys) = M.partition (\x -> case dataCons x of
        [(_, [(_, t)])] -> not $ packedOccurs (tyName x) t
        _ -> False
      ) (ddefs prog)
    tynames =
      M.mapKeys (\(Var x) -> unintern x)
      $ M.map (mkPolyNames . tyArgs <*> snd . head . snd . head . dataCons) newtys
    connames = S.fromList $ fst . head . dataCons <$> M.elems newtys
    fdefs = M.map (\d -> d { funTy=elimTyScheme tynames (funTy d)
                           , funBody=elimE connames tynames (ddefs prog) (funBody d)
                           }) (fundefs prog)

elimE :: S.Set String -> TyMap -> DDefs Ty0 -> Exp0 -> Exp0
elimE cns tns dds e0 = case e0 of
  DataConE _ty0 s [e]
    | S.member s cns -> f e
  DataConE _ty0 s es -> DataConE _ty0 s (f <$> es)
  VarE _ -> e0
  LitE _ -> e0
  CharE _ -> e0
  FloatE _ -> e0
  LitSymE _ -> e0
  AppE var ty es -> AppE var ty (f <$> es)
  PrimAppE p es -> PrimAppE (elimPrim tns p) (f <$> es)
  LetE (var, u, t, e1) e2 -> LetE (var, g <$> u, g t, f e1) (f e2)
  IfE e1 e2 e3 -> IfE (f e1) (f e2) (f e3)
  MkProdE es -> MkProdE (f <$> es)
  ProjE n e -> ProjE n (f e)
  CaseE e1 [(s, vars, e2)]
    | S.member s cns -> Ext (PolyAppE (Ext (LambdaE (second g <$> vars) (f e2))) (f e1))
  CaseE e x -> CaseE (f e) ((\(c, v, e1) -> (c, v, f e1)) <$> x)
  TimeIt e t b -> TimeIt (f e) (g t) b
  WithArenaE var e -> WithArenaE var (f e)
  SpawnE var ts es -> SpawnE var ts (f <$> es)

  Ext ext -> Ext (elimExt cns tns dds ext)
  _ -> e0
  where
    f = elimE cns tns dds
    g = elimTy tns

elimExt :: S.Set String -> TyMap -> DDefs Ty0 -> E0Ext Ty0 Ty0 -> E0Ext Ty0 Ty0
elimExt cns tns dds ext0 = case ext0 of
  LambdaE args applicand -> LambdaE (second g <$> args) (f applicand)
  FunRefE locs var -> FunRefE (g <$> locs) var
  PolyAppE pe1 pe2 -> PolyAppE (f pe1) (f pe2)
  BenchE var locs preexps bool -> BenchE var (g <$> locs) (f <$> preexps) bool
  ParE0 preexps -> ParE0 (f <$> preexps)
  PrintPacked dec preexp -> PrintPacked (g dec) (f preexp)
  CopyPacked dec preexp -> CopyPacked (g dec) (f preexp)
  TravPacked dec preexp -> TravPacked (g dec) (f preexp)
  L loc preexp -> L loc (f preexp)
  LinearExt (ReverseAppE pe1 pe2) -> LinearExt (ReverseAppE (f pe1) (f pe2))
  LinearExt (LseqE pe1 pe2) -> LinearExt (LseqE (f pe1) (f pe2))
  LinearExt (AliasE pe) -> LinearExt (AliasE (f pe))
  LinearExt (ToLinearE pe) -> LinearExt (ToLinearE (f pe))
  where
    f = elimE cns tns dds
    g = elimTy tns

elimPrim :: TyMap -> Prim Ty0 -> Prim Ty0
elimPrim tns p0 = case p0 of
  ErrorP s t -> ErrorP s (f t)
  DictInsertP t -> DictInsertP (f t)
  DictLookupP t -> DictLookupP (f t)
  DictEmptyP t -> DictEmptyP (f t)
  DictHasKeyP t -> DictHasKeyP (f t)
  PDictAllocP t1 t2 -> PDictAllocP (f t1) (f t2)
  PDictInsertP t1 t2 -> PDictInsertP (f t1) (f t2)
  PDictLookupP t1 t2 -> PDictLookupP (f t1) (f t2)
  PDictHasKeyP t1 t2 -> PDictHasKeyP (f t1) (f t2)
  PDictForkP t1 t2 -> PDictForkP (f t1) (f t2)
  PDictJoinP t1 t2 -> PDictJoinP (f t1) (f t2)
  LLAllocP t -> LLAllocP (f t)
  LLIsEmptyP t -> LLIsEmptyP (f t)
  LLConsP t -> LLConsP (f t)
  LLHeadP t -> LLHeadP (f t)
  LLTailP t -> LLTailP (f t)
  LLFreeP t -> LLFreeP (f t)
  LLCopyP t -> LLCopyP (f t)
  VAllocP t -> VAllocP (f t)
  VFreeP t -> VFreeP (f t)
  VFree2P t -> VFree2P (f t)
  VLengthP t -> VLengthP (f t)
  VNthP t -> VNthP (f t)
  VSliceP t -> VSliceP (f t)
  InplaceVUpdateP t -> InplaceVUpdateP (f t)
  VConcatP t -> VConcatP (f t)
  VSortP t -> VSortP (f t)
  InplaceVSortP t -> InplaceVSortP (f t)
  VMergeP t -> VMergeP (f t)
  ReadPackedFile ms s mVar t -> ReadPackedFile ms s mVar (f t)
  WritePackedFile s t -> WritePackedFile s (f t)
  ReadArrayFile m t -> ReadArrayFile m (f t)
  _ -> p0
  where
    f = elimTy tns

elimTyScheme :: TyMap -> TyScheme -> TyScheme
elimTyScheme tns (ForAll tvs t) = ForAll tvs (elimTy tns t)

elimTy :: TyMap -> Ty0 -> Ty0
elimTy tns t0 = case t0 of
  PackedTy s args -> maybe (PackedTy s (f <$> args)) ($ args) (M.lookup s tns)
  ProdTy ts -> ProdTy (f <$> ts)
  SymDictTy varMaybe t -> SymDictTy varMaybe (f t)
  VectorTy t -> VectorTy (f t)
  PDictTy tK tV -> PDictTy (f tK) (f tV)
  ListTy t -> ListTy (f t)
  _ -> t0
  where
    f = elimTy tns
