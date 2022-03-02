{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}

-- | A simple typechecker for the L3 language
-- It's very similar to the L1 typechecker
module Gibbon.L3.Typecheck
  ( tcProg, tcExp ) where


import Control.Monad.Except
import qualified Data.Map as M
import qualified Data.List as L
import Data.Maybe
import Prelude hiding (exp)

import Gibbon.Common
import Gibbon.L1.Typecheck hiding (tcProg, tcExp, ensureEqual, ensureEqualTy)
import Gibbon.L3.Syntax

-- | Typecheck a L1 expression
--
tcExp :: Bool -> DDefs3 -> Env2 Ty3 -> Exp3 -> TcM Ty3 Exp3
tcExp isPacked ddfs env exp =
  case exp of
    Ext ext ->
      case ext of
        -- One cursor in, (int, cursor') out
        ReadScalar s v -> do
          vty <- lookupVar env v exp
          ensureEqualTyModCursor exp vty CursorTy
          return $ ProdTy [scalarToTy s, CursorTy]

        -- Write int at cursor, and return a cursor
        WriteScalar s v rhs -> do
          vty  <- lookupVar env v exp
          vrhs <- go rhs
          ensureEqualTyModCursor exp vty CursorTy
          ensureEqualTyModCursor exp vrhs (scalarToTy s)
          return CursorTy

        -- One cursor in, (tag,cursor) out
        -- QUESTION: what should be the type of the tag ?  It's just an Int for now
        ReadTag v -> do
          vty  <- lookupVar env v exp
          ensureEqualTyModCursor exp vty CursorTy
          return $ ProdTy [IntTy, CursorTy]

        -- Write Tag at Cursor, and return a cursor
        WriteTag _dcon v -> do
          vty  <- lookupVar env v exp
          ensureEqualTyModCursor exp vty CursorTy
          return CursorTy

        ReadCursor v -> do
          vty <- lookupVar env v exp
          ensureEqualTyModCursor exp vty CursorTy
          return $ ProdTy [CursorTy, CursorTy]

        WriteCursor cur val -> do
          curty  <- lookupVar env cur exp
          ensureEqualTyModCursor exp curty CursorTy
          valty <- go val
          ensureEqualTyModCursor exp valty CursorTy
          return CursorTy

        ReadList v ty -> do
          vty <- lookupVar env v exp
          ensureEqualTyModCursor exp vty CursorTy
          return $ ProdTy [ListTy ty, CursorTy]

        WriteList cur val el_ty -> do
          curty  <- lookupVar env cur exp
          ensureEqualTyModCursor exp curty CursorTy
          valty <- go val
          ensureEqualTyModCursor exp valty (ListTy el_ty)
          return CursorTy

        ReadVector v ty -> do
          vty <- lookupVar env v exp
          ensureEqualTyModCursor exp vty CursorTy
          return $ ProdTy [VectorTy ty, CursorTy]

        WriteVector cur val el_ty -> do
          curty  <- lookupVar env cur exp
          ensureEqualTyModCursor exp curty CursorTy
          valty <- go val
          ensureEqualTyModCursor exp valty (VectorTy el_ty)
          return CursorTy

        -- Add a constant offset to a cursor variable
        AddCursor v rhs -> do
          vty  <- lookupVar env v exp
          ensureEqualTyModCursor exp vty CursorTy
          vrhs <- go rhs
          ensureEqualTyModCursor exp vrhs IntTy
          return CursorTy

        -- Subtract something from a cursor variable
        SubPtr v w -> do
          vty  <- lookupVar env v exp
          ensureEqualTyModCursor exp vty CursorTy
          wty  <- lookupVar env w exp
          ensureEqualTyModCursor exp wty CursorTy
          return IntTy

        -- Create a new buffer, and return a cursor
        NewBuffer{} -> return CursorTy
        NewParBuffer{} -> return CursorTy

        -- Create a scoped buffer, and return a cursor
        ScopedBuffer{} -> return CursorTy
        ScopedParBuffer{} -> return CursorTy

        EndOfBuffer{} -> return CursorTy

        MMapFileSize{} -> return IntTy

        -- Takes in start and end cursors, and returns an Int
        SizeOfPacked start end -> do
          sty  <- lookupVar env start exp
          ensureEqualTyModCursor exp sty CursorTy
          ety  <- lookupVar env end exp
          ensureEqualTyModCursor exp ety CursorTy
          return IntTy

        -- Takes in a variable, and returns an Int
        SizeOfScalar v -> do
          sty <- lookupVar env v exp
          if sty == IntTy || sty == FloatTy
          then return IntTy
          else throwError $ GenericTC ("Unknown scalar type: " ++ sdoc sty) exp

        -- The IntTy is just a placeholder. BoundsCheck is a side-effect
        BoundsCheck _ bound cur -> do
          rty <- lookupVar env bound exp
          ensureEqualTyModCursor exp rty CursorTy
          cty <- lookupVar env cur exp
          ensureEqualTyModCursor exp cty CursorTy
          return IntTy

        IndirectionBarrier _tycon (l1, end_r1, l2, end_r2) -> do
          l1_ty  <- lookupVar env l1 exp
          ensureEqualTyModCursor exp l1_ty CursorTy
          end_r1_ty  <- lookupVar env end_r1 exp
          ensureEqualTyModCursor exp end_r1_ty CursorTy
          l2_ty  <- lookupVar env l2 exp
          ensureEqualTyModCursor exp l2_ty CursorTy
          end_r2_ty  <- lookupVar env end_r2 exp
          ensureEqualTyModCursor exp end_r2_ty CursorTy
          return (ProdTy [])

        BumpArenaRefCount{} ->
          throwError $ GenericTC ("BumpArenaRefCount not handled.") exp

        RetE ls -> do
          tys <- mapM go ls
          pure (ProdTy tys)

        NullCursor -> return CursorTy

        GetCilkWorkerNum -> return IntTy

        LetAvail _ bod -> go bod

    -- All the other cases are exactly same as L1.Typecheck

    VarE v    -> lookupVar env v exp
    LitE _    -> return IntTy
    FloatE{}  -> return FloatTy
    LitSymE _ -> return SymTy

    AppE v locs ls -> do
      let funty =
            case (M.lookup v (fEnv env)) of
              Just ty -> ty
              Nothing -> error $ "Function not found: " ++ sdoc v ++ " while checking " ++
                                 sdoc exp

          (funInTys,funRetTy) = (inTys funty, outTy funty)

      -- Check that the expression does not have any locations
      case locs of
        [] -> return ()
        _  -> throwError $ GenericTC ("Expected the locations to be empty in L1. Got"
                                      ++ sdoc locs)
                           exp

      -- Check arity
      if (length ls) /= (length funInTys)
      then throwError $ GenericTC ("Arity mismatch. Expected:" ++ show (length funInTys) ++
                                   " Got:" ++ show (length ls)) exp
      else pure ()

      -- Check argument type
      argTys <- mapM go ls

      let combAr (SymDictTy (Just v1) _, SymDictTy (Just v2) _) m = M.insert v2 v1 m
          combAr _ m = m
          arMap = L.foldr combAr M.empty $ fragileZip argTys funInTys

          subDictTy m (SymDictTy (Just w) ty) =
              case M.lookup w m of
                Just w' -> SymDictTy (Just w') ty
                Nothing -> error $ ("Cannot match up arena for dictionary in function application: " ++ sdoc exp)
          subDictTy _ ty = ty

          subFunInTys = L.map (subDictTy arMap) funInTys
          subFunOutTy = subDictTy arMap funRetTy
      _ <- mapM (\(a,b) -> ensureEqualTyModCursor exp a b) (zip subFunInTys argTys)
      return subFunOutTy

    PrimAppE pr es -> do
      -- Special case because we can't lookup the type of the function pointer
      let es' = case pr of
                  VSortP{} -> init es
                  InplaceVSortP{} -> init es
                  _ -> es
      tys <- mapM go es'
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
            _ <- ensureEqualTyModCursor (es !! 0) BoolTy (tys !! 0)
            _ <- ensureEqualTyModCursor (es !! 1) BoolTy (tys !! 1)
            pure BoolTy

          int_ops = do
            len2
            _ <- ensureEqualTyModCursor (es !! 0) IntTy (tys !! 0)
            _ <- ensureEqualTyModCursor (es !! 1) IntTy (tys !! 1)
            pure IntTy

          float_ops = do
            len2
            _ <- ensureEqualTy (es !! 0) FloatTy (tys !! 0)
            _ <- ensureEqualTy (es !! 1) FloatTy (tys !! 1)
            pure FloatTy

          int_cmps = do
            len2
            _ <- ensureEqualTyModCursor (es !! 0) IntTy (tys !! 0)
            _ <- ensureEqualTyModCursor (es !! 1) IntTy (tys !! 1)
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
          _ <- ensureEqualTyModCursor (es !! 0) SymTy (tys !! 0)
          _ <- ensureEqualTyModCursor (es !! 1) SymTy (tys !! 1)
          return BoolTy

        EqBenchProgP _ -> do
          len0
          return BoolTy

        RandP -> return IntTy
        FRandP-> return FloatTy
        FSqrtP -> do
          len1
          ensureEqualTy exp FloatTy (tys !! 0)
          return FloatTy

        FTanP -> do
          len1
          ensureEqualTy exp FloatTy (tys !! 0)
          return FloatTy

        FloatToIntP -> do
          len1
          _ <- ensureEqualTy exp FloatTy (tys !! 0)
          return IntTy

        IntToFloatP -> do
          len1
          _ <- ensureEqualTy exp IntTy (tys !! 0)
          return FloatTy

        SizeParam -> do
          len0
          return IntTy

        IsBig -> do
          len2
          let [ity, ety] = tys
          ensureEqualTy exp ity IntTy
          ensureEqualTy exp ety CursorTy
          pure BoolTy

        PrintInt -> do
          len1
          _ <- ensureEqualTy (es !! 0) IntTy (tys !! 0)
          return (ProdTy [])

        PrintFloat -> do
          len1
          _ <- ensureEqualTy (es !! 0) FloatTy (tys !! 0)
          return (ProdTy [])

        PrintBool -> do
          len1
          _ <- ensureEqualTy (es !! 0) BoolTy (tys !! 0)
          return (ProdTy [])

        PrintSym -> do
          len1
          _ <- ensureEqualTy (es !! 0) SymTy (tys !! 0)
          return (ProdTy [])

        ReadInt -> do
          len0
          return IntTy

        SymSetEmpty -> do
          len0
          return SymSetTy

        SymSetInsert -> do
          len2
          _ <- ensureEqualTy (es !! 0) SymSetTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) SymTy (tys !! 1)
          return SymSetTy

        SymSetContains -> do
          len2
          _ <- ensureEqualTy (es !! 0) SymSetTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) SymTy (tys !! 1)
          return BoolTy

        SymHashEmpty -> do
          len0
          return SymHashTy

        SymHashInsert -> do
          len3
          _ <- ensureEqualTy (es !! 0) SymHashTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) SymTy (tys !! 1)
          _ <- ensureEqualTy (es !! 2) SymTy (tys !! 2)
          return SymHashTy

        SymHashLookup -> do
          len2
          _ <- ensureEqualTy (es !! 0) SymHashTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) SymTy (tys !! 1)
          return SymTy

        SymHashContains -> do
          len2
          _ <- ensureEqualTy (es !! 0) SymHashTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) SymTy (tys !! 1)
          return BoolTy

        DictEmptyP _ty -> do
          len1
          let [a] = tys
          _ <- ensureEqualTyModCursor exp ArenaTy a
          let (VarE var) = es !! 0
          return $ SymDictTy (Just var) CursorTy

        DictInsertP _ty -> do
          len4
          let [a,_d,k,v] = tys
          let (VarE var) = es !! 0
          _ <- ensureEqualTyModCursor exp ArenaTy a
          _ <- ensureEqualTyModCursor exp SymTy k
          _ <- ensureEqualTyModCursor exp CursorTy v
          return $ SymDictTy (Just var) CursorTy

        DictLookupP _ty -> do
          len2
          let [_d,k] = tys
          _ <- ensureEqualTyModCursor exp SymTy k
          return CursorTy

        DictHasKeyP _ty -> do
          len2
          let [_d,k] = tys
          -- _ <- ensureEqualTyNoLoc exp (SymDictTy ty) d
          _ <- ensureEqualTyModCursor exp SymTy k
          return BoolTy

        ErrorP _str ty -> do
          len0
          return ty

        ReadPackedFile _fp _tycon _reg ty -> do
          len0
          if isPacked
          then return CursorTy
          else return ty

        WritePackedFile _ ty
           | PackedTy{} <- ty  -> do
             len1
             let [packed_ty] = tys
             _ <- ensureEqualTyModCursor exp packed_ty ty
             pure (ProdTy [])
           | otherwise -> error $ "writePackedFile expects a packed type. Given" ++ sdoc ty

        ReadArrayFile _ ty -> do
          len0
          if isValidListElemTy ty
          then return (VectorTy ty)
          else throwError $ GenericTC "Not a valid list type" exp

        RequestEndOf  -> error "RequestEndOf shouldn't occur in a L3 program."
        RequestSizeOf -> error "RequestSizeOf shouldn't occur in a L3 program."

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
          _ <- ensureEqualTy (es !! 0) IntHashTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) SymTy (tys !! 1)
          _ <- ensureEqualTy (es !! 2) IntTy (tys !! 2)
          return IntHashTy

        IntHashLookup -> do
          len2
          _ <- ensureEqualTy (es !! 0) IntHashTy (tys !! 0)
          _ <- ensureEqualTy (es !! 1) SymTy (tys !! 1)
          return IntTy

        Write3dPpmFile{} -> throwError $ GenericTC "Write3dPpmFile not handled yet" exp



    LetE (v,[],SymDictTy _ _pty, rhs) e -> do
      tyRhs <- go rhs
      case tyRhs of
        SymDictTy ar _ ->
            do  unless (isJust ar) $ throwError $ GenericTC "Expected arena variable annotation" rhs
                let env' = extendEnv env [(v,SymDictTy ar CursorTy)]
                tcExp isPacked ddfs env' e
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
      _ <- ensureEqualTyModCursor exp tyRhs ty
      let env' = extendEnv env [(v,ty)]
      -- Check body
      tcExp isPacked ddfs env' e

    IfE tst consq alt -> do
      -- Check if the test is a boolean
      tyTst <- go tst
      _ <- ensureEqualTyModCursor exp tyTst BoolTy

      -- Check if both branches match
      tyConsq <- go consq
      tyAlt   <- go alt

      -- _ <- ensureEqualTyModCursor exp tyConsq tyAlt
      -- if tyConsq == tyAlt
      -- then return tyConsq
      -- else throwError $ GenericTC ("If branches have mismatched types:"
      --                              ++ sdoc tyConsq ++ ", " ++ sdoc tyAlt) exp
      ensureEqualTyModCursor exp tyConsq tyAlt

    MkProdE [] -> return $ ProdTy []

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
        [_one] -> do
          when (tye /= CursorTy && not (isPackedTy tye)) $
            throwError $ GenericTC ("Case scrutinee should be packed, or have a cursor type. Got"
                                    ++ sdoc tye) e
          tcCases isPacked ddfs env cs
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
        sequence_ [ ensureEqualTyModCursor e ty1 ty2
                  | (ty1,ty2,e) <- zip3 args tys es]
        return $ PackedTy dcTy loc

    TimeIt e _ty _b -> do
      -- Before flatten, _ty is always (PackedTy "DUMMY_TY" ())
      -- enforce ty == _ty in strict mode ?
      ty <- go e
      return ty

    SpawnE fn locs args -> go (AppE fn locs args)
    SyncE -> pure voidTy

    WithArenaE v e -> do
      let env' = extendVEnv v ArenaTy env
      tcExp isPacked ddfs env' e

    MapE{}  -> throwError $ UnsupportedExpTC exp
    FoldE{} -> throwError $ UnsupportedExpTC exp

    -- oth -> error $ "L1.tcExp : TODO " ++ sdoc oth

  where
    go = tcExp isPacked ddfs env
    checkListElemTy el_ty =
      if isValidListElemTy el_ty
      then pure ()
      else throwError $ GenericTC ("Gibbon-TODO: Lists of only scalars or flat products of scalars are allowed. Got" ++ sdoc el_ty) exp


-- | Typecheck a L1 program
--
tcProg :: Bool -> Prog3 -> PassM Prog3
tcProg isPacked prg@Prog{ddefs,fundefs,mainExp} = do

  -- Handle functions
  mapM_ fd $ M.elems fundefs

  -- Handle main expression
  -- We don't change the type of mainExp to have cursors. So if it's type was `Packed`,
  -- it's still Packed, while the expression actually has type CursorTy.
  -- They're essentially the same.
  case mainExp of
    Nothing -> return ()
    Just (e,ty)  ->
      let res = runExcept $ tcExp isPacked ddefs env e
      in case res of
        Left err -> error $ sdoc err
        Right ty' -> if tyEq ty ty'
                     then return ()
                     else error $ "Expected type " ++ sdoc ty ++ "and got type " ++ sdoc ty'

  -- Identity function for now.
  return prg

  where
    env = progToEnv prg
    tyEq CursorTy PackedTy{} = True
    tyEq PackedTy{} CursorTy = True
    tyEq ty1 ty2 =
      case ty1 of
        PackedTy{}  -> ty2 == ProdTy [CursorTy,CursorTy] || ty1 == ty2
        ProdTy tys2 -> let ProdTy tys1 = ty1
                       in  all (\(a,b) -> tyEq a b) (zip tys1 tys2)
        _ -> ty1 == ty2

    -- fd :: forall e l . FunDef Ty1 Exp -> PassM ()
    fd FunDef{funArgs,funTy,funBody} = do
      let (intys, outty) = funTy
          venv = M.fromList (zip funArgs intys)
          env' = Env2 venv (fEnv env)
          res = runExcept $ tcExp isPacked ddefs env' funBody
      case res of
        Left err -> error $ sdoc err
        Right ty -> if ty `compareModCursor` outty
                    then return ()
                    else error $ "Expected type " ++ (sdoc outty)
                         ++ " and got type " ++ (sdoc ty) ++ "\n" ++ (sdoc funBody)

      return ()


tcCases :: Bool -> DDefs3 -> Env2 Ty3 -> [(DataCon, [(Var, ())], Exp3)] -> TcM Ty3 (Exp3)
tcCases isPacked ddfs env cs = do
  tys <- forM cs $ \(c,args',rhs) -> do
           let args  = L.map fst args'
               targs = map packedToCursor $ lookupDataCon ddfs c
               env'  = extendEnv env (zip args targs)
           tcExp isPacked ddfs env' rhs
  foldM_ (\acc (ex,ty) -> ensureEqualTyModCursor ex ty acc)
            -- if ty == acc
            -- then return acc
            -- else throwError $ GenericTC ("Case branches have mismatched types: "
            --                              ++ sdoc acc ++ ", " ++ sdoc ty) ex)
         (head tys) (zipWith (\ty (_,_,ex) -> (ex,ty)) tys cs)
  return $ head tys

-- | Ensure that two things are equal.
-- Includes an expression for error reporting.
ensureEqual :: Exp3 -> String -> Ty3 -> Ty3 -> TcM Ty3 (Exp3)
ensureEqual exp str (SymDictTy ar1 _) (SymDictTy ar2 _) =
    if ar1 == ar2
    then return $ SymDictTy ar1 CursorTy
    else throwError $ GenericTC str exp
ensureEqual exp str a b = if a == b
                          then return a
                          else throwError $ GenericTC str exp


-- | Ensure that two types are equal.
-- Includes an expression for error reporting.
ensureEqualTy :: Exp3 -> Ty3 -> Ty3 -> TcM Ty3 (Exp3)
ensureEqualTy exp a b = ensureEqual exp ("Expected these types to be the same: "
                                         ++ (sdoc a) ++ ", " ++ (sdoc b)) a b

ensureEqualTyModCursor :: Exp3 -> Ty3 -> Ty3 -> TcM Ty3 (Exp3)
ensureEqualTyModCursor _exp CursorTy (PackedTy _ _) = return CursorTy
ensureEqualTyModCursor _exp (PackedTy _ _) CursorTy = return CursorTy
ensureEqualTyModCursor _exp IntTy CursorTy = return CursorTy
ensureEqualTyModCursor _exp CursorTy IntTy = return CursorTy
ensureEqualTyModCursor exp (ProdTy ls1) (ProdTy ls2) =
  sequence_ [ ensureEqualTyModCursor exp ty1 ty2 | (ty1,ty2) <- zip ls1 ls2] >>= \_ -> return (packedToCursor (ProdTy ls1))
ensureEqualTyModCursor exp a b = ensureEqualTy exp a b

packedToCursor :: Ty3 -> Ty3
packedToCursor (PackedTy _ _) = CursorTy
packedToCursor (ProdTy tys) = ProdTy $ map packedToCursor tys
packedToCursor ty = ty

compareModCursor :: Ty3 -> Ty3 -> Bool
compareModCursor CursorTy (PackedTy _ _) = True
compareModCursor (PackedTy _ _) CursorTy = True
compareModCursor ty1 ty2 = ty1 == ty2

ensureEqualTyNoLoc :: Exp3 -> Ty3 -> Ty3 -> TcM Ty3 (Exp3)
ensureEqualTyNoLoc exp t1 t2 =
  case (t1,t2) of
    (SymDictTy _ _ty1, SymDictTy _ _ty2) -> return t1
        -- do ty1' <- L2.dummyTyLocs ty1
        --    ty2' <- L2.dummyTyLocs ty2
        --    ensureEqualTyNoLoc exp ty1' ty2'
    (PackedTy dc1 _, PackedTy dc2 _) -> if dc1 == dc2
                                        then return t1
                                        else ensureEqualTy exp t1 t2
    (ProdTy tys1, ProdTy tys2) -> do
        checks <- return $ L.map (\(ty1,ty2) -> ensureEqualTyNoLoc exp ty1 ty2) (zip tys1 tys2)
        forM_ checks $ \c -> do
            let c' = runExcept c
            case c' of
              Left err -> throwError err
              Right _  -> return ()
        return t1
    _ -> ensureEqualTy exp t1 t2
