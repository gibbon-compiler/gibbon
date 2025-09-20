module Gibbon.Passes.FollowPtrs
  ( followPtrs )
  where

import qualified Data.Map as M
-- import qualified Data.Set as S
import qualified Data.List as L
import           Data.Foldable ( foldrM )
import           Data.Maybe ( fromJust )

import           Gibbon.Common
import           Gibbon.Language
import           Gibbon.L2.Syntax as L2
import Gibbon.DynFlags
import Gibbon.L3.Syntax (E3Ext(AddCursor))

--------------------------------------------------------------------------------

-- | Generate code for indirection and redirection pointer branches in the case expression.
followPtrs :: Prog2 -> PassM Prog2
followPtrs (Prog ddefs fundefs mainExp) = do
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

    go env out_ty funName funArgs funTy e =
      case e of
          CaseE scrt brs -> do
            let VarE scrtv = scrt
                PackedTy tycon scrt_loc = env # scrtv
                DDef{dataCons} = lookupDDef ddefs tycon
            flags <- getDynFlags
            let no_copies = gopt Opt_No_RemoveCopies flags
            if no_copies
            then do
              indir_ptrv <- gensym "indr"
              indir_ptrv_loc <- freshCommonLoc "indr" scrt_loc
              callv <- gensym "call"
              wc <- gensym "wildcard"
              indir_ptrloc <- freshCommonLoc "case" scrt_loc

              endofs <- mapM (\lr -> case lr of
                                            EndOf lrm -> do 
                                                         let loc = lrmLoc lrm 
                                                         freshCommonLoc "endof" loc
                              ) (locRets funTy)

              --endofs <- mapM (\_ -> gensym "endof") (locRets funTy)
              --let endofs' = map Single endofs
              let args = foldr (\v acc -> if v == scrtv
                                          then ((VarE indir_ptrv) : acc)
                                          else (VarE v : acc))
                              [] funArgs
              let in_locs = foldr (\loc acc -> if loc ==  scrt_loc then ((indir_ptrloc) : acc) else (loc : acc)) [] (inLocVars funTy)
              let out_locs = outLocVars funTy
              -- [VS: 09/14/2025]
              -- In case an output location, that's passed to the function call. 
              -- for an SoA location, we cannot simply pass this directly. 
              -- Since we do this by value, we need to update the SoA location, 
              -- because bounds checking may have updated the value of the location.
              -- Note that we only need to update the non packed locations + the data constructor buffer.
              -- Other packed types will be updated by the function that traverses it.
              (new_out_locs, new_loc_bnds) <- foldrM (\locvar (nl, bnds) -> case locvar of 
                                                                                  SoA dloc flocs -> do 
                                                                                              -- unpack all locations in the SoA location. 
                                                                                              let unpack_dcon = LetLocE (singleLocVar dloc) (GetDataConLocSoA locvar)
                                                                                              let unpack_flds = map (\((dcon, idx), floc) -> do 
                                                                                                                                              let flet = LetLocE floc (GetFieldLocSoA (dcon, idx) locvar) 
                                                                                                                                               in flet
                                                                                                                    ) flocs
                                                                                              -- make a new name for this loc_var
                                                                                              new_locvar <- freshCommonLoc "copy" locvar
                                                                                              let new_don_loc = getDconLoc new_locvar
                                                                                              -- The data con loc should be unpacked and updated by bounds check. 
                                                                                              -- from design of the compiler 
                                                                                              let new_don_let = LetLocE new_don_loc (AfterConstantLE 0 (singleLocVar dloc))
                                                                                              let new_fld_locs = getAllFieldLocsSoA new_locvar
                                                                                              new_fld_lets <- foldrM (\((dcon, idx), nfloc) flts -> do 
                                                                                                                                                let ty = (lookupDataCon ddefs dcon) !! idx
                                                                                                                                                  in case (ty) of
                                                                                                                                                            PackedTy{} -> do 
                                                                                                                                                                  let let_for_fld = LetLocE nfloc (GetFieldLocSoA (dcon, idx) locvar)
                                                                                                                                                                   in pure $ flts ++ [let_for_fld]
                                                                                                                                                            _ -> do 
                                                                                                                                                                  let let_for_fld = LetLocE nfloc (AfterConstantLE 0 (getFieldLoc (dcon, idx) locvar))
                                                                                                                                                                    in pure $ flts ++ [let_for_fld]
                                                                                                                                                       ) [] new_fld_locs
                                                                                              let new_soa_loc_let = LetLocE new_locvar (GenSoALoc new_don_loc new_fld_locs)
                                                                                              return $ (nl ++ [new_locvar], bnds ++ [unpack_dcon] ++ unpack_flds ++ [new_don_let] ++ new_fld_lets ++ [new_soa_loc_let]) 
                                                                                         
                                                                                  -- no need to update single location variables
                                                                                  Single{} -> return $ (nl ++ [locvar], bnds)
                                                     ) ([], [])  out_locs
              let redir_dcon = fst $ fromJust $ L.find (isRedirectionTag . fst) dataCons
              let redir_bod = (if isPrinterName funName then LetE (wc,[],ProdTy[],PrimAppE PrintSym [LitSymE (toVar " ->r ")]) else id) $
                              LetE (callv,endofs,out_ty,AppE funName (in_locs ++ new_out_locs) args) $
                              Ext (RetE endofs callv)
              let redir_bod' = foldr (\bnd bod -> Ext $ bnd bod) redir_bod new_loc_bnds
              let redir_br = (redir_dcon,[(indir_ptrv,(indir_ptrloc))],redir_bod')
              ----------------------------------------
              (pure (CaseE scrt (brs ++ [redir_br])))
            else do
              indir_ptrv <- gensym "indr"
              indir_ptrv_loc <- freshCommonLoc "indr" scrt_loc
              indir_ptrloc <- freshCommonLoc "case" scrt_loc
              jump <- freshCommonLoc "jump" scrt_loc
              callv <- gensym "call"
              let _effs = arrEffs funTy
              endofs <- mapM (\lr -> case lr of
                                            EndOf lrm -> do 
                                                         let loc = lrmLoc lrm 
                                                         freshCommonLoc "endof" loc
                              ) (locRets funTy)
              --let endofs' = map Single endofs
              let ret_endofs = foldr (\(end, (EndOf (LRM loc _ _))) acc ->
                                        if loc == scrt_loc
                                        then (jump) : acc
                                        else end : acc)
                              []
                               (zip endofs (locRets funTy))
              let args = foldr (\v acc -> if v == scrtv
                                          then ((VarE indir_ptrv) : acc)
                                          else (VarE v : acc))
                              [] funArgs
              let in_locs = foldr (\loc acc -> if loc ==  scrt_loc then ((indir_ptrloc) : acc) else (loc : acc)) [] (inLocVars funTy)
              let out_locs = outLocVars funTy
              wc <- gensym "wildcard"
              -- TODO, VS: the jump location should change
              -- We need to unpack the SoA location of the scrut
              -- We only need to do this for the data constructor.
              -- the assumption is that the SoA cursor will be 
              -- written after the tag. So its going to be a 
              -- Cursor Array. We will cast pass this to the
              -- call a cast should be added automatically.
              
              -- Get data con loc of scrut (indir_ptrloc)
              -- Bump this up by 8 
              -- Make the new SoA location with the data con loc 
              -- Field locs will all be the same
              indir_br <- case scrt_loc of 
                  SoA{} -> do 
                    let data_con_let = LetLocE (getDconLoc scrt_loc) (GetDataConLocSoA scrt_loc)
                    let new_jump_dloc = LetLocE (getDconLoc jump) (AfterConstantLE 9 ((getDconLoc scrt_loc)))
                    let unpack_fld_lets = foldr (\((dcon, idx), lc) acc ->  acc ++ [LetLocE lc (GetFieldLocSoA (dcon, idx) scrt_loc)]) [] (getAllFieldLocsSoA scrt_loc)

                    let indir_bod = Ext $ LetLocE (jump) (GenSoALoc (getDconLoc jump) (getAllFieldLocsSoA scrt_loc) ) $
                                 (if isPrinterName funName then LetE (wc,[],ProdTy[],PrimAppE PrintSym [LitSymE (toVar " ->i ")]) else id) $
                                 LetE (callv,endofs,out_ty,AppE funName (in_locs ++ out_locs) args) $
                                 Ext (RetE ret_endofs callv)
                    let indir_bod' = foldr (\l b -> Ext $ l b) indir_bod ([data_con_let] ++ [new_jump_dloc] ++ unpack_fld_lets)
                    let indir_dcon = fst $ fromJust $ L.find (isIndirectionTag . fst) dataCons
                    return $ (indir_dcon,[(indir_ptrv,(indir_ptrloc))],indir_bod')
                  Single{} -> do
                    let indir_bod = Ext $ LetLocE (jump) (AfterConstantLE 8 (indir_ptrloc)) $
                            (if isPrinterName funName then LetE (wc,[],ProdTy[],PrimAppE PrintSym [LitSymE (toVar " ->i ")]) else id) $
                            LetE (callv,endofs,out_ty,AppE funName (in_locs ++ out_locs) args) $
                            Ext (RetE ret_endofs callv)
                    let indir_dcon = fst $ fromJust $ L.find (isIndirectionTag . fst) dataCons
                    return $ (indir_dcon,[(indir_ptrv,(indir_ptrloc))],indir_bod)
                    
              ----------------------------------------
              -- [VS: 09/14/2025]
              -- In case an output location, that's passed to the function call. 
              -- for an SoA location, we cannot simply pass this directly. 
              -- Since we do this by value, we need to update the SoA location, 
              -- because bounds checking may have updated the value of the location.
              -- Note that we only need to update the non packed locations + the data constructor buffer.
              -- Other packed types will be updated by the function that traverses it.
              (new_out_locs, new_loc_bnds) <- foldrM (\locvar (nl, bnds) -> case locvar of 
                                                                                  SoA dloc flocs -> do 
                                                                                              -- unpack all locations in the SoA location. 
                                                                                              let unpack_dcon = LetLocE (singleLocVar dloc) (GetDataConLocSoA locvar)
                                                                                              let unpack_flds = map (\((dcon, idx), floc) -> do 
                                                                                                                                              let flet = LetLocE floc (GetFieldLocSoA (dcon, idx) locvar) 
                                                                                                                                               in flet
                                                                                                                    ) flocs
                                                                                              -- make a new name for this loc_var
                                                                                              new_locvar <- freshCommonLoc "copy" locvar
                                                                                              let new_don_loc = getDconLoc new_locvar
                                                                                              -- The data con loc should be unpacked and updated by bounds check. 
                                                                                              -- from design of the compiler 
                                                                                              let new_don_let = LetLocE new_don_loc (AfterConstantLE 0 (singleLocVar dloc))
                                                                                              let new_fld_locs = getAllFieldLocsSoA new_locvar
                                                                                              new_fld_lets <- foldrM (\((dcon, idx), nfloc) flts -> do 
                                                                                                                                                let ty = (lookupDataCon ddefs dcon) !! idx
                                                                                                                                                  in case (ty) of
                                                                                                                                                            PackedTy{} -> do 
                                                                                                                                                                  let let_for_fld = LetLocE nfloc (GetFieldLocSoA (dcon, idx) locvar)
                                                                                                                                                                   in pure $ flts ++ [let_for_fld]
                                                                                                                                                            _ -> do 
                                                                                                                                                                  let let_for_fld = LetLocE nfloc (AfterConstantLE 0 (getFieldLoc (dcon, idx) locvar))
                                                                                                                                                                    in pure $ flts ++ [let_for_fld]
                                                                                                                                                       ) [] new_fld_locs
                                                                                              let new_soa_loc_let = LetLocE new_locvar (GenSoALoc new_don_loc new_fld_locs)
                                                                                              return $ (nl ++ [new_locvar], bnds ++ [unpack_dcon] ++ unpack_flds ++ [new_don_let] ++ new_fld_lets ++ [new_soa_loc_let]) 
                                                                                         
                                                                                  -- no need to update single location variables
                                                                                  Single{} -> return $ (nl ++ [locvar], bnds)
                                                     ) ([], [])  out_locs
              let redir_dcon = fst $ fromJust $ L.find (isRedirectionTag . fst) dataCons
              let redir_bod = (if isPrinterName funName then LetE (wc,[],ProdTy[],PrimAppE PrintSym [LitSymE (toVar " ->r ")]) else id) $
                             LetE (callv,endofs,out_ty,AppE funName (in_locs ++ new_out_locs) args) $
                             Ext (RetE endofs callv)
              let redir_bod' = foldr (\bnd bod -> Ext $ bnd bod) redir_bod new_loc_bnds
              let redir_br = (redir_dcon,[(indir_ptrv,(indir_ptrloc))],redir_bod')
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
