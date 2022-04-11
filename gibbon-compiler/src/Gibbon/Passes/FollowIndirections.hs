module Gibbon.Passes.FollowIndirections
  ( followIndirections )
  where

import qualified Data.Map as M
-- import qualified Data.Set as S
import qualified Data.List as L
-- import           Data.Foldable ( foldrM )
import           Data.Maybe ( fromJust )

import           Gibbon.Common
import           Gibbon.Language
import           Gibbon.L2.Syntax as L2

--------------------------------------------------------------------------------

followIndirections :: Prog2 -> PassM Prog2
followIndirections (Prog ddefs fundefs mainExp) = do
    fds' <- mapM gofun (M.elems fundefs)
    let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
    pure $ Prog ddefs fundefs' mainExp
  where
    gofun :: FunDef2 -> PassM FunDef2
    gofun f@FunDef{funName,funArgs,funBody,funTy} = do
      let in_tys = arrIns funTy
      let out_ty = arrOut funTy
      funBody' <- go (M.fromList (zip funArgs in_tys)) out_ty funName funArgs funTy funBody
      pure $ f { funBody = funBody' }

    go env  out_ty funName funArgs funTy e =
      case e of
          CaseE scrt brs -> do
            let VarE scrtv = scrt
                PackedTy tycon scrt_loc = env # scrtv
                DDef{dataCons} = lookupDDef ddefs tycon

            indir_ptrv <- gensym "indr"
            indir_ptrloc <- gensym "case"
            jump <- gensym "jump"
            callv <- gensym "call"
            let _effs = arrEffs funTy
            endofs <- mapM (\_ -> gensym "endof") (locRets funTy)
            let ret_endofs = foldr (\(end, (EndOf (LRM loc _ _))) acc ->
                                      if loc == scrt_loc
                                      then jump : acc
                                      else end : acc)
                             []
                             (zip endofs (locRets funTy))
            let args = foldr (\v acc -> if v == scrtv
                                        then ((VarE indir_ptrv) : acc)
                                        else (VarE v : acc))
                             [] funArgs
            let in_locs = foldr (\loc acc -> if loc ==  scrt_loc then (indir_ptrv : acc) else (loc : acc)) [] (inLocVars funTy)
            let out_locs = outLocVars funTy
            wc <- gensym "wildcard"
            let indir_bod = Ext $ LetLocE jump (AfterConstantLE 8 indir_ptrloc) $
                            (if isPrinterName funName then LetE (wc,[],ProdTy[],PrimAppE PrintSym [LitSymE (toVar " ->i ")]) else id) $
                            LetE (callv,endofs,out_ty,AppE funName (in_locs ++ out_locs) args) $
                            Ext (RetE ret_endofs callv)
            let indir_dcon = fst $ fromJust $ L.find (isIndirectionTag . fst) dataCons
            let indir_br = (indir_dcon,[(indir_ptrv,indir_ptrloc)],indir_bod)
            ----------------------------------------
            let redir_dcon = fst $ fromJust $ L.find (isRedirectionTag . fst) dataCons
            let redir_bod = (if isPrinterName funName then LetE (wc,[],ProdTy[],PrimAppE PrintSym [LitSymE (toVar " ->r ")]) else id) $
                            LetE (callv,endofs,out_ty,AppE funName (in_locs ++ out_locs) args) $
                            Ext (RetE endofs callv)
            let redir_br = (redir_dcon,[(indir_ptrv,indir_ptrloc)],redir_bod)
            ----------------------------------------
            (pure (CaseE scrt (brs ++ [indir_br,redir_br])))

          IfE a b c -> do
            a' <- go env  out_ty funName funArgs funTy a
            b' <- go env  out_ty funName funArgs funTy b
            c' <- go env  out_ty funName funArgs funTy c
            pure $ IfE a' b' c'

          WithArenaE v bod -> (WithArenaE v) <$> go env  out_ty funName funArgs funTy bod

          LetE (v,locs,ty,rhs) bod ->
            LetE (v,locs,ty,rhs) <$> go (M.insert v ty env)  out_ty funName funArgs funTy  bod

          Ext (LetLocE loc rhs bod) ->
            Ext <$> (LetLocE loc rhs) <$> go env  out_ty funName funArgs funTy  bod

          Ext (LetRegionE reg sz ty bod) ->
            Ext <$> (LetRegionE reg sz ty) <$> go env  out_ty funName funArgs funTy  bod

          Ext (LetParRegionE reg sz ty bod) ->
            Ext <$> (LetParRegionE reg sz ty) <$> go env  out_ty funName funArgs funTy  bod

          _ -> pure e
