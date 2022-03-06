{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Gibbon.L1.Typecheck
  ( -- * The two main typechecker functions
    tcProg, tcExp

    -- * Helpers
  , TCError(..)
  , extendEnv, lookupVar, tcProj, checkLen, ensureEqual, ensureEqualTy, TcM
  )
where


import Control.Monad.Except
import Data.Map as M
import Data.Set as S
import Data.List as L
import Data.Maybe
import Text.PrettyPrint
import Text.PrettyPrint.GenericPretty

import Gibbon.Common
import Gibbon.L1.Syntax as L1
import Gibbon.DynFlags
import Prelude hiding (exp)

--------------------------------------------------------------------------------

-- | Typecheck a L1 expression
--
tcExp :: DDefs1 -> Env2 Ty1 -> Exp1 -> TcM Ty1 Exp1
tcExp ddfs env exp =
  case exp of
    VarE v    -> lookupVar env v exp
    LitE _    -> return IntTy
    FloatE{}  -> return FloatTy
    LitSymE _ -> return SymTy

    AppE v locs ls -> do
      let funty =
            case (M.lookup v (fEnv env)) of
              Just ty -> ty
              Nothing -> error $ "Function not found: " ++ sdoc v ++ " while checking " ++
                                 sdoc exp ++ "\nat "
      -- Check that the expression does not have any locations
      case locs of
        [] -> return ()
        _  -> throwError $ GenericTC ("Expected the locations to be empty in L1. Got"
                                      ++ sdoc locs)
                           exp

      -- Get argument types
      argTys <- mapM go ls

      -- Check arity
      if (length ls) /= (length argTys)
      then throwError $ GenericTC ("Arity mismatch. Expected:" ++ show (length argTys) ++
                                   " Got:" ++ show (length ls)) exp
      else pure ()

      let (funInTys,funRetTy) = (inTys funty, outTy funty)

          combAr (SymDictTy (Just v1) _, SymDictTy (Just v2) _) m = M.insert v2 v1 m
          combAr _ m = m
          arMap = L.foldr combAr M.empty $ fragileZip argTys funInTys

          subDictTy m (SymDictTy (Just w) ty) =
              case M.lookup w m of
                Just w' -> SymDictTy (Just w') ty
                Nothing -> error $ ("Cannot match up arena for dictionary in function application: " ++ sdoc exp)
          subDictTy _ ty = ty

          subFunInTys = L.map (subDictTy arMap) funInTys
          subFunOutTy = subDictTy arMap funRetTy

      _ <- mapM (\(a,b) -> ensureEqualTy exp a b) (fragileZip subFunInTys argTys)
      return subFunOutTy

    PrimAppE pr es -> do
      -- Special case because we can't lookup the type of the function pointer
      tys <- case pr of
               VSortP{} -> mapM go (init es)
               InplaceVSortP{} -> mapM go (init es)
               _ -> mapM go es

      let len0 = checkLen exp pr 0 es
          len1 = checkLen exp pr 1 es
          len2 = checkLen exp pr 2 es
          len3 = checkLen exp pr 3 es
          len4 = checkLen exp pr 4 es

          mk_bools = do
            len0
            pure BoolTy

          bool_ops = do
            len2
            _ <- ensureEqualTy (es !!! 0) BoolTy (tys !!! 0)
            _ <- ensureEqualTy (es !!! 1) BoolTy (tys !!! 1)
            pure BoolTy

          int_ops = do
            len2
            _ <- ensureEqualTy (es !!! 0) IntTy (tys !!! 0)
            _ <- ensureEqualTy (es !!! 1) IntTy (tys !!! 1)
            pure IntTy

          float_ops = do
            len2
            _ <- ensureEqualTy (es !! 0) FloatTy (tys !! 0)
            _ <- ensureEqualTy (es !! 1) FloatTy (tys !! 1)
            pure FloatTy

          int_cmps = do
            len2
            _ <- ensureEqualTy (es !!! 0) IntTy (tys !!! 0)
            _ <- ensureEqualTy (es !!! 1) IntTy (tys !!! 1)
            pure BoolTy

          float_cmps = do
            len2
            _ <- ensureEqualTy (es !! 0) FloatTy (tys !! 0)
            _ <- ensureEqualTy (es !! 1) FloatTy (tys !! 1)
            pure BoolTy

      case pr of
        MkTrue  -> mk_bools
        MkFalse -> mk_bools
        AddP    -> int_ops
        SubP    -> int_ops
        MulP    -> int_ops
        DivP    -> int_ops
        ModP    -> int_ops
        ExpP    -> int_ops
        FAddP   -> float_ops
        FSubP   -> float_ops
        FMulP   -> float_ops
        FDivP   -> float_ops
        FExpP   -> float_ops
        EqIntP  -> int_cmps
        LtP     -> int_cmps
        GtP     -> int_cmps
        LtEqP   -> int_cmps
        GtEqP   -> int_cmps
        EqFloatP -> float_cmps
        FLtP     -> float_cmps
        FGtP     -> float_cmps
        FLtEqP   -> float_cmps
        FGtEqP   -> float_cmps
        OrP     -> bool_ops
        AndP    -> bool_ops

        Gensym -> len0 >>= \_ -> pure SymTy

        EqSymP -> do
          len2
          _ <- ensureEqualTy (es !!! 0) SymTy (tys !!! 0)
          _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
          return BoolTy

        EqBenchProgP _ -> do
          len0
          return BoolTy

        RandP -> return IntTy
        FRandP -> return FloatTy
        FSqrtP -> do
          len1
          _ <- ensureEqualTy exp FloatTy (tys !! 0)
          return FloatTy

        FTanP -> do
          len1
          _ <- ensureEqualTy exp FloatTy (tys !! 0)
          return FloatTy

        FloatToIntP -> do
          len1
          _ <- ensureEqualTy exp FloatTy (tys !! 0)
          return IntTy

        IntToFloatP -> do
          len1
          _ <- ensureEqualTy exp IntTy (tys !! 0)
          return FloatTy

        PrintInt -> do
          len1
          _ <- ensureEqualTy (es !!! 0) IntTy (tys !!! 0)
          return (ProdTy [])

        PrintFloat -> do
          len1
          _ <- ensureEqualTy (es !!! 0) FloatTy (tys !!! 0)
          return (ProdTy [])

        PrintBool -> do
          len1
          _ <- ensureEqualTy (es !!! 0) BoolTy (tys !!! 0)
          return (ProdTy [])

        PrintSym -> do
          len1
          _ <- ensureEqualTy (es !!! 0) SymTy (tys !!! 0)
          return (ProdTy [])

        ReadInt -> do
          len0
          return IntTy

        SymSetEmpty -> do
          len0
          return SymSetTy

        SymSetInsert -> do
          len2
          _ <- ensureEqualTy (es !!! 0) SymSetTy (tys !!! 0)
          _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
          return SymSetTy

        SymSetContains -> do
          len2
          _ <- ensureEqualTy (es !!! 0) SymSetTy (tys !!! 0)
          _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
          return BoolTy

        SymHashEmpty -> do
          len0
          return SymHashTy

        SymHashInsert -> do
          len3
          _ <- ensureEqualTy (es !!! 0) SymHashTy (tys !!! 0)
          _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
          _ <- ensureEqualTy (es !!! 2) SymTy (tys !!! 2)
          return SymHashTy

        SymHashLookup -> do
          len2
          _ <- ensureEqualTy (es !!! 0) SymHashTy (tys !!! 0)
          _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
          return SymTy

        SymHashContains -> do
          len2
          _ <- ensureEqualTy (es !!! 0) SymHashTy (tys !!! 0)
          _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
          return BoolTy

        DictEmptyP ty -> do
          len1
          let [a] = tys
          _ <- ensureEqualTy exp ArenaTy a
          case (es !! 0) of
            (VarE var) -> do ensureArenaScope exp env $ Just var
                             return $ SymDictTy (Just var) ty
            _ -> throwError $ GenericTC "Expected arena variable argument" exp

        DictInsertP ty -> do
          len4
          let [a,d,k,v] = tys
          _ <- ensureEqualTy exp ArenaTy a
          case d of
            SymDictTy ar dty -> do _ <- ensureEqualTy exp SymTy k
                                   _ <- ensureEqualTy exp ty v
                                   _ <- ensureEqualTy exp ty dty
                                   ensureArenaScope exp env ar
                                   case es !!! 0 of
                                     (VarE var) -> do ensureArenaScope exp env $ Just var
                                                      return $ SymDictTy (Just var) ty
                                     _ -> throwError $ GenericTC "Expected arena variable argument" exp
            _ -> throwError $ GenericTC "Expected SymDictTy" exp

        DictLookupP ty -> do
          len2
          let [d,k] = tys
          case d of
            SymDictTy ar dty -> do _ <- ensureEqualTy exp SymTy k
                                   _ <- ensureEqualTy exp ty dty
                                   -- dbgTrace 3 (show $ vEnv env) $ return ()
                                   ensureArenaScope exp env ar
                                   return ty
            _ -> throwError $ GenericTC "Expected SymDictTy" exp

        DictHasKeyP ty -> do
          len2
          let [d,k] = tys
          case d of
            SymDictTy ar dty -> do _ <- ensureEqualTy exp SymTy k
                                   _ <- ensureEqualTy exp ty dty
                                   ensureArenaScope exp env ar
                                   return BoolTy
            _ -> throwError $ GenericTC "Expected SymDictTy" exp

        ErrorP _str ty -> do
          len0
          return ty

        SizeParam -> do
          len0
          return IntTy

        IsBig -> do
          len2
          let [ity,ety] = tys
          _ <- ensureEqualTy exp ity IntTy
          if isPackedTy ety
          then pure BoolTy
          else error $ "L1.Typecheck: IsBig expects a Packed value. Got: " ++ sdoc ety

        ReadPackedFile _fp _tycon _reg ty -> do
          len0
          return ty

        WritePackedFile _ ty
           | PackedTy{} <- ty  -> do
             len1
             let [packed_ty] = tys
             _ <- ensureEqualTy exp packed_ty ty
             pure (ProdTy [])
           | otherwise -> error $ "writePackedFile expects a packed type. Given" ++ sdoc ty

        ReadArrayFile _ ty -> do
          len0
          if isValidListElemTy ty
          then return (VectorTy ty)
          else throwError $ GenericTC "Not a valid list type" exp

        RequestEndOf -> do
          len1
          case (es !!! 0) of
            VarE{} -> return CursorTy
                -- if isPackedTy (tys !!! 0)
                -- then return CursorTy
                -- else throwError $ GenericTC "Expected PackedTy" exp
            _ -> throwError $ GenericTC "Expected a variable argument" exp

        RequestSizeOf -> do
          len1
          case (es !! 0) of
            VarE{} -> if isPackedTy (tys !! 0)
                      then return IntTy
                      else case (tys !! 0) of
                             SymTy -> return IntTy
                             IntTy -> return IntTy
                             _ -> throwError $ GenericTC "Expected PackedTy" exp
            _ -> throwError $ GenericTC "Expected a variable argument" exp

        VAllocP elty -> do
          len1
          checkListElemTy elty
          let [i] = tys
          _ <- ensureEqualTy (es !! 0) IntTy i
          pure (VectorTy elty)

        VFreeP elty -> do
          len1
          checkListElemTy elty
          let [i] = tys
          _ <- ensureEqualTy (es !! 0) (VectorTy elty) i
          pure (ProdTy [])

        VFree2P elty -> do
          len1
          checkListElemTy elty
          let [i] = tys
          _ <- ensureEqualTy (es !! 0) (VectorTy elty) i
          pure (ProdTy [])

        VLengthP elty -> do
          len1
          checkListElemTy elty
          let [ls] = tys
          _ <- ensureEqualTy (es !! 0) (VectorTy elty) ls
          pure IntTy

        VNthP elty -> do
          len2
          checkListElemTy elty
          let [ls, i] = tys
          _ <- ensureEqualTy (es !! 0) (VectorTy elty) ls
          _ <- ensureEqualTy (es !! 1) IntTy i
          pure elty

        VSliceP elty -> do
          len3
          checkListElemTy elty
          let [from,to,ls] = tys
          _ <- ensureEqualTy (es !! 0) IntTy from
          _ <- ensureEqualTy (es !! 1) IntTy to
          _ <- ensureEqualTy (es !! 2) (VectorTy elty) ls
          pure (VectorTy elty)

        InplaceVUpdateP elty -> do
          len3
          checkListElemTy elty
          let [ls,i,x] = tys
          _ <- ensureEqualTy (es !! 0) (VectorTy elty) ls
          _ <- ensureEqualTy (es !! 1) IntTy i
          _ <- ensureEqualTy (es !! 2) elty x
          pure (VectorTy elty)

        VConcatP elty -> do
          len1
          checkListElemTy elty
          let [ls] = tys
          _ <- ensureEqualTy (es !! 0) (VectorTy (VectorTy elty)) ls
          pure (VectorTy elty)

        -- Given that the first argument is a list of type (VectorTy t),
        -- ensure that the 2nd argument is function reference of type:
        -- ty -> ty -> IntTy
        VSortP elty ->
          case (es !! 1) of
            VarE f -> do
              len2
              let [ls] = tys
                  fn_ty@(in_tys, ret_ty) = lookupFEnv f env
                  err x = throwError $ GenericTC ("vsort: Expected a sort function of type (ty -> ty -> Bool). Got"++ sdoc x) exp
              _ <- ensureEqualTy (es !! 0) (VectorTy elty) ls
              case in_tys of
                [a,b] -> do
                   -- [2021.05.08]: looks suspicious
                   _ <- ensureEqualTy (es !! 1) a elty
                   _ <- ensureEqualTy (es !! 1) b elty
                   _ <- ensureEqualTy (es !! 1) ret_ty IntTy
                   pure (VectorTy elty)
                _ -> err fn_ty
            oth -> throwError $ GenericTC ("vsort: function pointer has to be a variable reference. Got"++ sdoc oth) exp

        InplaceVSortP elty -> go (PrimAppE (VSortP elty) es)

        VMergeP elty -> do
          len2
          checkListElemTy elty
          let [ls1,ls2] = tys
          _ <- ensureEqualTy (es !! 0) (VectorTy elty) ls1
          _ <- ensureEqualTy (es !! 1) (VectorTy elty) ls2
          pure (VectorTy elty)


        PDictInsertP kty vty -> do
          len3
          checkListElemTy kty
          checkListElemTy vty
          let [key, val, dict] = tys
          _ <- ensureEqualTy (es !! 0) key kty
          _ <- ensureEqualTy (es !! 1) val vty
          _ <- ensureEqualTy (es !! 2) dict (PDictTy kty vty)
          pure (PDictTy kty vty)

        PDictLookupP kty vty -> do
          len2
          checkListElemTy kty
          checkListElemTy vty
          let [key, dict] = tys
          _ <- ensureEqualTy (es !! 0) key kty
          _ <- ensureEqualTy (es !! 0) dict (PDictTy kty vty)
          pure (vty)

        PDictAllocP kty vty -> do
          len0
          checkListElemTy kty
          checkListElemTy vty
          pure (PDictTy kty vty)

        PDictHasKeyP kty vty -> do
          len2
          checkListElemTy kty
          checkListElemTy vty
          let [key, dict] = tys
          _ <- ensureEqualTy (es !! 0) key kty
          _ <- ensureEqualTy (es !! 0) dict (PDictTy kty vty)
          pure (BoolTy)

        PDictForkP kty vty -> do
          len1
          checkListElemTy kty
          checkListElemTy vty
          let [dict] = tys
          _ <- ensureEqualTy (es !! 0) dict (PDictTy kty vty)
          pure (ProdTy [PDictTy kty vty, PDictTy kty vty])

        PDictJoinP kty vty -> do
          len2
          checkListElemTy kty
          checkListElemTy vty
          let [dict1, dict2] = tys
          _ <- ensureEqualTy (es !! 0) dict1 (PDictTy kty vty)
          _ <- ensureEqualTy (es !! 0) dict2 (PDictTy kty vty)
          pure (PDictTy kty vty)

        LLAllocP elty -> do
          len0
          checkListElemTy elty
          pure (ListTy elty)

        LLIsEmptyP elty -> do
          len1
          checkListElemTy elty
          let [ll] = tys
          _ <- ensureEqualTy (es !! 0) ll (ListTy elty)
          pure (BoolTy)

        LLConsP elty -> do
          len2
          checkListElemTy elty
          let [elt, ll] = tys
          _ <- ensureEqualTy (es !! 0) elt elty
          _ <- ensureEqualTy (es !! 1) ll (ListTy elty)
          pure (ListTy elty)

        LLHeadP elty -> do
          len1
          checkListElemTy elty
          let [ll] = tys
          _ <- ensureEqualTy (es !! 0) ll (ListTy elty)
          pure (elty)

        LLTailP elty -> do
          len1
          checkListElemTy elty
          let [ll] = tys
          _ <- ensureEqualTy (es !! 0) ll (ListTy elty)
          pure (ListTy elty)

        LLFreeP elty -> do
          len1
          checkListElemTy elty
          let [i] = tys
          _ <- ensureEqualTy (es !! 0) (ListTy elty) i
          pure (ProdTy [])

        LLFree2P elty -> do
          len1
          checkListElemTy elty
          let [i] = tys
          _ <- ensureEqualTy (es !! 0) (ListTy elty) i
          pure (ProdTy [])

        LLCopyP elty -> do
          len1
          checkListElemTy elty
          let [i] = tys
          _ <- ensureEqualTy (es !! 0) (ListTy elty) i
          pure (ListTy elty)

        GetNumProcessors -> do
          len0
          pure IntTy

        IntHashEmpty -> do
          len0
          return IntHashTy

        IntHashInsert -> do
          len3
          _ <- ensureEqualTy (es !!! 0) IntHashTy (tys !!! 0)
          _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
          _ <- ensureEqualTy (es !!! 2) IntTy (tys !!! 2)
          return IntHashTy

        IntHashLookup -> do
          len2
          _ <- ensureEqualTy (es !!! 0) IntHashTy (tys !!! 0)
          _ <- ensureEqualTy (es !!! 1) SymTy (tys !!! 1)
          return IntTy

        Write3dPpmFile{} -> throwError $ GenericTC "Write3dPpmFile not handled yet" exp


    LetE (v,[],SymDictTy _ pty, rhs) e -> do
      tyRhs <- go rhs
      case tyRhs of
        SymDictTy ar pty' ->
            do  _ <- ensureEqualTy exp pty pty'
                unless (isJust ar) $ throwError $ GenericTC "Expected arena variable annotation" rhs
                let env' = extendEnv env [(v,SymDictTy ar pty')]
                tcExp ddfs env' e
        _ -> throwError $ GenericTC ("Expected expression to be SymDict type:" ++ sdoc rhs) exp

    LetE (v,locs,ty,rhs) e -> do
      -- Check that the expression does not have any locations
      case locs of
        [] -> return ()
        _  -> throwError $ GenericTC ("Expected the locations to be empty in L1. Got"
                                      ++ sdoc locs)
                           exp
      -- Check RHS
      tyRhs <- go rhs
      _ <- ensureEqualTy exp tyRhs ty
      let env' = extendEnv env [(v,ty)]
      -- Check body
      tcExp ddfs env' e

    IfE tst consq alt -> do
      -- Check if the test is a boolean
      tyTst <- go tst
      _ <- ensureEqualTy exp tyTst BoolTy

      -- Check if both branches match
      tyConsq <- go consq
      tyAlt   <- go alt

      -- _ <- ensureEqualTy exp tyConsq tyAlt
      if tyConsq == tyAlt
      then return tyConsq
      else throwError $ GenericTC ("If branches have mismatched types:"
                                   ++ sdoc tyConsq ++ ", " ++ sdoc tyAlt) exp


    MkProdE es -> do
      tys <- mapM go es
      return $ ProdTy tys

    ProjE i e -> do
      ty  <- go e
      tyi <- tcProj exp i ty
      return tyi

    CaseE e cs -> do
      tye  <- go e
      let tycons = L.map (getTyOfDataCon ddfs . (\(a,_,_) -> a)) cs
      case L.nub tycons of
        [one] -> do
          -- _ <- ensureEqualTy exp (PackedTy one ()) tye
          let (PackedTy t _l) = tye
          if one == t
          then return ()
          else error$ "Expected these to be the same: " ++ one ++ " & " ++ sdoc t
          tcCases ddfs env cs
        oth   -> throwError $ GenericTC ("Case branches have mismatched types: " ++ sdoc oth
                                         ++" , in " ++ sdoc exp) exp

    DataConE loc dc es -> do
      tys <- mapM go es
      let dcTy = getTyOfDataCon ddfs dc
          args = lookupDataCon ddfs dc
      if length args /= length es
      then throwError $ GenericTC ("Invalid argument length: " ++ sdoc es) exp
      else do
        -- Check if arguments match with expected datacon types
        sequence_ [ ensureEqualTy e ty1 ty2
                  | (ty1,ty2,e) <- zip3 args tys es]
        return $ PackedTy dcTy loc

    TimeIt e _ty _b -> do
      -- Before flatten, _ty is always (PackedTy "DUMMY_TY" ())
      -- enforce ty == _ty in strict mode ?
      ty <- go e
      return ty

    SpawnE v locs ls -> do
      ty <- go (AppE v locs ls)
      if isScalarTy ty || isPackedTy ty
      then pure ty
      else case ty of
             ProdTy tys ->
               case L.filter isPackedTy tys of
                 []    -> pure ty
                 [_one]-> pure ty
                 _     -> error $ "Gibbon-TODO: Product types not allowed in SpawnE. Got: " ++ sdoc ty
             VectorTy{} -> pure ty
             _ -> error "L1.Typecheck: SpawnE; type shouldn't be anything else."

    SyncE -> pure voidTy

    WithArenaE v e -> do
      let env' = extendEnv env [(v,ArenaTy)]
      tcExp ddfs env' e

    Ext (BenchE fn tyapps args _b) -> do
      go (AppE fn tyapps args)

    Ext (AddFixed{})-> -- throwError $ GenericTC "AddFixed not handled." exp
      pure CursorTy

    MapE{} -> error $ "L1.Typecheck: TODO: " ++ sdoc exp
    FoldE{} -> error $ "L1.Typecheck: TODO: " ++ sdoc exp

  where
    go = tcExp ddfs env

    checkListElemTy el_ty =
      if isValidListElemTy el_ty
      then pure ()
      else throwError $ GenericTC ("Gibbon-TODO: Lists of only scalars or flat products of scalars are allowed. Got" ++ sdoc el_ty) exp

-- | Typecheck a L1 program
--
tcProg :: Prog1 -> PassM Prog1
tcProg prg@Prog{ddefs,fundefs,mainExp} = do
  -- Get flags to check if we're in packed mode
  flags <- getDynFlags

  -- check ddefs
  mapM_ checkDDef $ M.elems ddefs

  -- Handle functions
  mapM_ fd $ M.elems fundefs

  -- Handle main expression.
  -- Run the typechecker on the expression, and update it's type in the program
  -- (the parser initializes the main expression with the void type).
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (e,main_ty) -> do
                  let res = runExcept $ tcExp ddefs env e
                  case res of
                    Left err -> error $ sdoc err
                    Right ty ->
                      -- The program was just parsed, the type of the
                      -- expression must be *inferred*.
                      -- Otherwise, fail if the types don't match.
                      if main_ty == voidTy
                      then return $ Just (e, ty)
                      else if main_ty == ty
                           -- Fail if the main expression is packed and we're in packed mode
                           then if (not $ hasPacked ty) || (not $ gopt Opt_Packed flags)
                                then return $ Just (e, ty)
                                else error $ "Main expression has type " ++ sdoc ty ++ ", but it must be a simple (non-packed) type, such as " ++ (sdoc (IntTy :: Ty1)) ++ "."
                           else error $ "Expected type " ++ sdoc main_ty ++ " but got " ++ sdoc ty

  return prg { mainExp = mainExp' }

  where
    env = L1.progToEnv prg

    checkDDef DDef{dataCons} = do
        mapM_ go dataCons
      where
        go (dcon, tys) = do
          let tys' = (L.map snd tys)
              mb_firstPacked = L.findIndex isPackedTy tys'
              scalars = findIndices (not . isPackedTy) tys'
          case mb_firstPacked of
            Nothing -> return ()
            Just fp -> case scalars of
                         [] -> return ()
                         _ -> if (last scalars) > fp
                              then error ("Gibbon-TODO: Constructor " ++ dcon ++
                                          " has a scalar field after a packed field which isn't" ++
                                          " allowed at the moment.")
                              else return ()


    -- fd :: forall e l . FunDef Ty1 Exp -> SyM ()
    fd FunDef{funName,funArgs,funTy,funBody} = do
      let (argTys,retty) = funTy
          venv = M.fromList (zip funArgs argTys)
          env' = Env2 venv (fEnv env)
          res  = runExcept $ tcExp ddefs env' funBody
      case res of
        Left err -> error $ sdoc err
        Right ty -> if (length $ getPackedTys retty) > 1
                    then error ("Gibbon-TODO: Functions cannot return multiple packed values; "
                                ++ "check " ++ sdoc funName)
                    else if ty == retty
                    then return ()
                    else error $ "Expected type " ++ (sdoc retty)
                              ++ " and got type " ++ (sdoc ty)
      return ()

--------------------------------------------------------------------------------
-- Helpers

data TCError exp = GenericTC String  exp
                 | VarNotFoundTC Var exp
                 | UnsupportedExpTC  exp
  deriving (Show, Eq, Ord, Generic)


instance (Out exp) => Out (TCError exp) where
  doc tce =
    case tce of
      GenericTC str ex    -> text str $$ colon <+> doc ex
      VarNotFoundTC v ex  -> text "Var" <+> doc v <+> text "not found. Checking: " $$
                             colon <+> doc ex
      UnsupportedExpTC ex -> text "Unsupported expression:" $$
                             colon <+> doc ex

type TcM a exp =  Except (TCError exp) a

extendEnv :: Env2 (UrTy l) -> [(Var, (UrTy l))] -> Env2 (UrTy l)
extendEnv (Env2 vEnv fEnv) ((v,ty):rest) = extendEnv (Env2 (M.insert v ty vEnv) fEnv) rest
extendEnv env [] = env


lookupVar :: Env2 (UrTy l) -> Var -> PreExp e () (UrTy ()) -> TcM (UrTy l) (PreExp e () (UrTy ()))
lookupVar env var exp =
    case M.lookup var $ vEnv env of
      Nothing -> throwError $ VarNotFoundTC var exp
      Just ty -> return ty


tcProj :: (Out l) => PreExp e () (UrTy ()) -> Int -> (UrTy l) -> TcM (UrTy l) (PreExp e () (UrTy ()))
tcProj _ i (ProdTy tys) = return $ tys !!! i
tcProj e _i ty = throwError $ GenericTC ("Projection from non-tuple type " ++ (sdoc ty)) e


tcCases :: DDefs Ty1 -> Env2 Ty1 -> [(DataCon, [(Var, ())], Exp1)] -> TcM Ty1 Exp1
tcCases ddfs env cs = do
  tys <- forM cs $ \(c,args',rhs) -> do
           let args  = L.map fst args'
               targs = lookupDataCon ddfs c
               env'  = extendEnv env (zip args targs)
           tcExp ddfs env' rhs
  foldM_ (\acc (ex,ty) ->
            if ty == acc
            then return acc
            else throwError $ GenericTC ("Case branches have mismatched types: "
                                         ++ sdoc acc ++ ", " ++ sdoc ty) ex)
         (head tys) (zipWith (\ty (_,_,ex) -> (ex,ty)) tys cs)
  return $ head tys


checkLen :: (Out op, Out arg) => PreExp e () (UrTy ()) -> op -> Int -> [arg] ->
            TcM () (PreExp e () (UrTy ()))
checkLen expr pr n ls =
  if length ls == n
  then return ()
  else throwError $ GenericTC ("Wrong number of arguments to "++sdoc pr++
                               ".\nExpected "++sdoc n++", received "
                                ++sdoc (length ls)++":\n  "++sdoc ls)
                    expr

-- | Ensure that two things are equal.
-- Includes an expression for error reporting.
ensureEqual :: (Eq l) => PreExp e () (UrTy ()) -> String -> (UrTy l) ->
               (UrTy l) -> TcM (UrTy l) (PreExp e () (UrTy ()))
ensureEqual exp str a b = if a == b
                          then return a
                          else throwError $ GenericTC str exp


-- | Ensure that two types are equal.
-- Includes an expression for error reporting.
-- ensureEqualTy :: (Eq l, Out l) => PreExp e () (UrTy ()) -> (UrTy l) -> (UrTy l) ->
--                  TcM (UrTy l) PreExp e () (UrTy ())
ensureEqualTy :: PreExp e () (UrTy ()) -> Ty1 -> Ty1 -> TcM Ty1 (PreExp e () (UrTy ()))
ensureEqualTy _exp CursorTy IntTy = return CursorTy
ensureEqualTy _exp IntTy CursorTy = return CursorTy
ensureEqualTy exp a b = ensureEqual exp ("Expected these types to be the same: "
                                         ++ (sdoc a) ++ ", " ++ (sdoc b)) a b

ensureArenaScope :: MonadError (TCError exp) m => exp -> Env2 a -> Maybe Var -> m ()
ensureArenaScope exp env ar =
    case ar of
      Nothing -> throwError $ GenericTC "Expected arena annotation" exp
      Just var -> unless (S.member var . M.keysSet . vEnv $ env) $
                  throwError $ GenericTC ("Expected arena in scope: " ++ sdoc var) exp
