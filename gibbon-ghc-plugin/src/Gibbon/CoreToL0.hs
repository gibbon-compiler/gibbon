module Gibbon.CoreToL0 ( coreToL0 ) where

{- Translating GHC Core into Gibbon's L0 frontend
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- GHC Core.
data Expr b
  = Var   Id
  | Lit   Literal
  | App   (Expr b) (Arg b)
  | Lam   b (Expr b)
  | Let   (Bind b) (Expr b)
  | Case  (Expr b) b Type [Alt b]
  | Cast  (Expr b) Coercion
  | Tick  CoreTickish (Expr b)
  | Type  Type
  | Coercion Coercion


-- Gibbon's expressions.
data PreExp (ext :: Type -> Type -> Type) loc dec =
     VarE Var
   | LitE Int
   | FloatE Double
   | LitSymE Var
   | AppE Var [loc] [EXP]
   | PrimAppE (Prim dec) [EXP]
   | LetE (Var,[loc],dec, EXP) EXP
   | IfE EXP EXP EXP
   | MkProdE   [EXP]
   | ProjE Int EXP
   | CaseE EXP [(DataCon, [(Var,loc)], EXP)]
   | DataConE loc DataCon [EXP]
   | TimeIt EXP dec Bool
   | WithArenaE Var EXP
   | SpawnE Var [loc] [EXP]
   | SyncE
   | Ext (ext loc dec)

-- | The extension point for L0.
data E0Ext loc dec =
   LambdaE [(Var,dec)] (PreExp E0Ext loc dec)
 | PolyAppE (PreExp E0Ext loc dec) (PreExp E0Ext loc dec)
 | FunRefE [loc] Var
 | BenchE Var [loc] [(PreExp E0Ext loc dec)] Bool
 | ParE0 [(PreExp E0Ext loc dec)]
 | PrintPacked dec (PreExp E0Ext loc dec)
 | CopyPacked dec (PreExp E0Ext loc dec)
 | TravPacked dec (PreExp E0Ext loc dec)
 | L Loc.Loc (PreExp E0Ext loc dec)
 | LinearExt (LinearExt loc dec)

-- | Linear types primitives.
data LinearExt loc dec =
    ReverseAppE (PreExp E0Ext loc dec) (PreExp E0Ext loc dec)
  | LseqE (PreExp E0Ext loc dec) (PreExp E0Ext loc dec)
  | AliasE (PreExp E0Ext loc dec)
  | ToLinearE (PreExp E0Ext loc dec)


-}

import qualified GHC.Plugins as GHC
import qualified GHC.Core.Multiplicity as GHC
import qualified GHC.Core.TyCo.Rep as GHC

import qualified Gibbon.Common as Gib
import qualified Gibbon.Pretty as Gib
import qualified Gibbon.L0.Syntax as Gib

import qualified Data.Map as M
import Gibbon.Utils


--------------------------------------------------------------------------------

coreToL0 :: [GHC.DataCon] -> [(GHC.Id, GHC.CoreExpr)] -> GHC.CoreM Gib.Prog0
coreToL0 dcons _funs = do
    let ddefs = convertDcons dcons
    Gib.dbgTraceIt (Gib.sdoc ddefs) (pure ())
    pure $ Gib.Prog { Gib.ddefs = ddefs
                    , Gib.fundefs = M.empty
                    , Gib.mainExp = Nothing
                    }

convertDcons :: [GHC.DataCon] -> Gib.DDefs0
convertDcons dcons =
    foldr go M.empty dcons
  where
    go :: GHC.DataCon -> Gib.DDefs0 -> Gib.DDefs0
    go dcon ddefs
        | GHC.isVanillaDataCon dcon
        , tycon <- GHC.dataConTyCon dcon
        , GHC.isVanillaAlgTyCon tycon
        , tyname <- GHC.tyConName tycon
        , tyname_str <- nameToString tyname
        , tyname_var <- Gib.toVar tyname_str
        = case tyname_str of
              "Int"   -> ddefs
              "Float" -> ddefs
              "Bool"  -> ddefs
              _ -> let tyvars =  GHC.tyConTyVars tycon
                       tyvars_var = map (Gib.UserTv . Gib.toVar . varToString) tyvars
                       dcname = GHC.dataConName dcon
                       (_,_,_,_,dcon_args,_dcon_res) = GHC.dataConFullSig dcon
                       dcon_tys = map (\ty -> (False,ghcScaledTyToGibTy ty)) dcon_args
                       dcon_gib = (nameToString dcname, dcon_tys)
                   in case M.lookup tyname_var ddefs of
                          Nothing   ->
                              let ddef = Gib.DDef tyname_var tyvars_var [dcon_gib]
                              in M.insert tyname_var ddef ddefs
                          Just ddef ->
                              let ddef' = ddef { Gib.dataCons = dcon_gib : (Gib.dataCons ddef) }
                              in M.insert tyname_var ddef' ddefs


        | tycon <- GHC.dataConTyCon dcon
        = GHC.pprSorry ("Non-vanilla datacons not supported yet:") (GHC.ppr (dcon,tycon))


ghcScaledTyToGibTy :: GHC.Scaled GHC.Type -> Gib.Ty0
ghcScaledTyToGibTy (GHC.Scaled _ ty) = ghcTyToGibTy ty

ghcTyToGibTy :: GHC.Type -> Gib.Ty0
ghcTyToGibTy ty
    | GHC.AppTy{} <- ty
    = let (arg_tys,res_ty) = GHC.splitPiTys ty
      in GHC.pprSorry "todo(1):" (GHC.ppr (arg_tys,res_ty))

    | GHC.ForAllTy{} <- ty
    = GHC.pprSorry "todo(2):" (GHC.ppr ty)

    | GHC.TyConApp tycon tyargs <- ty
    = if not (length tyargs == GHC.tyConArity tycon)
        then GHC.pprSorry "unsaturated TyConApp:" (GHC.ppr ty)
        else let tyname_str = nameToString (GHC.tyConName tycon) in
                 case tyname_str of
                     "Int" -> Gib.IntTy
                     "Float" -> Gib.FloatTy
                     "Bool" -> Gib.BoolTy
                     _oth  -> let tyvars = GHC.tyConTyVars tycon
                                  tyvars_var = map (Gib.TyVar . Gib.UserTv . Gib.toVar . varToString) tyvars
                              in Gib.PackedTy tyname_str tyvars_var
                     -- GHC.pprSorry "todo(3):" (GHC.ppr ty)

    | GHC.TyVarTy v <- ty
    = Gib.TyVar (Gib.UserTv (Gib.toVar (varToString v)))

    | otherwise
    = GHC.pprSorry "todo(4):" (GHC.ppr ty)
