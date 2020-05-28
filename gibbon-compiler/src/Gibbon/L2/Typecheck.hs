{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fdefer-typed-holes #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

-- |

module Gibbon.L2.Typecheck
    ( tcExp, tcProg, TCError(..)
    , RegionSet(..)
    , LocationTypeState(..)
    , ConstraintSet(..)
    , LocConstraint(..)
    , Aliased, TcM )
    where

import           Control.DeepSeq
import           Control.Monad.Except
import           Data.Foldable ( foldlM )
import qualified Data.Set as S
import           Data.List as L
import qualified Data.Map as M
import           Data.Maybe
import           Text.PrettyPrint.GenericPretty
import           Debug.Trace

import           Gibbon.Common
import           Gibbon.L2.Syntax as L2
-- import qualified Gibbon.L1.Syntax as L1

-- | Constraints on locations.  Used during typechecking.  Roughly analogous to LocExp.
data LocConstraint = StartOfC LocVar Region -- ^ Location is equal to start of this region.
                   -- Can't attach haddocks to data constructor arguments with < GHC 8.4.2
                   -- See https://github.com/haskell/haddock/pull/709.
                   | AfterConstantC Int     -- Number of bytes after.
                                    LocVar  -- Location which is before
                                    LocVar  -- Location which is after
                   | AfterVariableC Var     -- Name of variable v. This loc is size(v) bytes after.
                                    LocVar  -- Location which is before
                                    LocVar  -- Location which is after
                   | InRegionC LocVar Region -- Location is somewher within this region.
  deriving (Read, Show, Eq, Ord, Generic, NFData, Out)


-- | A set of constraints (which are re-used location expressions)
-- which encode relationships between locations. These are used by the
-- type checker to verify that locations are used correctly.
--
-- The following are valid constraints:
--  * StartOfC LocVar Region
--  * AfterConstantC Int LocVar LocVar
--  * AfterVariableC Var LocVar LocVar
--  * InRegionC LocVar Region
--  * FromEndC
--
-- While the first four can appear in syntax before RouteEnds, the fifth
-- (fromEnd) should only be introduced by the RouteEnds pass.
newtype ConstraintSet = ConstraintSet { constraintSet :: S.Set LocConstraint }
  deriving (Read, Show, Eq, Ord, Generic, NFData, Out)

-- | A location has been aliased if we have taken an offset of it while introducing a new
-- location. These show up in the LocationTypeState below.
type Aliased = Bool

-- | A map from locations to their type state. This tracks the current state of a location
-- at a certain point in a program. The type checker threads this through by taking an
-- input map that represents the location states before checking a particular expression,
-- and returns an output map that represents the location states after checking that
-- particular expression.
-- All we need to know in this map is whether each location is an input or output location,
-- and whether we've taken an offset of the location in a letloc form.
newtype LocationTypeState = LocationTypeState
    {
      tsmap :: M.Map LocVar (Modality,Aliased)
      -- ^ Each location has a modality and may have had an offset taken.
    }
    deriving (Read,Show,Eq,Ord, Generic, NFData, Out)

-- | A region set is (as you would expect) a set of regions. They are the
-- regions that are currently live while checking a particular expression.
newtype RegionSet = RegionSet { regSet :: S.Set Var }
  deriving (Read, Show, Eq, Ord, Generic, NFData)


-- | Shorthand for located expressions
type Exp = Exp2

-- | These are the kinds of errors that the type checker may throw. There are a
-- few named errors that I thought would be common, like variables not being
-- found, locations being used incorrectly, etc. For other errors, there's a
-- GenericTC form that takes some expression and string
-- (containing an error message).
data TCError = GenericTC String Exp
             | VarNotFoundTC Var Exp
             | UnsupportedExpTC Exp
             | LocationTC String Exp LocVar LocVar
             | ModalityTC String Exp LocVar LocationTypeState
               deriving (Read,Eq,Ord,Generic,NFData)

instance Show TCError where
    show (GenericTC str e) = "Error typechecking L2 Program\nIn the expression:\n" ++ (sdoc e) ++ "\n" ++ str ++ "\n"
    show (VarNotFoundTC v e) = "Variable not found: " ++ (show v) ++ "\nIn the expression:\n" ++ (sdoc e) ++ "\n"
    show (UnsupportedExpTC e) = "Unsupported expression:\n" ++ (sdoc e) ++ "\n"
    show (LocationTC str e lv1 lv2) = "Location typechecking error: " ++ str ++ "\nIn the expression:\n" ++ (sdoc e)
                                      ++ "\nLocations: " ++ (show lv1) ++ ", " ++ (show lv2) ++ "\n"
    show (ModalityTC str e lv lts) = "Modality typechecking error: " ++ str ++ "\nIn the expression:\n" ++ (sdoc e)
                                     ++ "\nLocation: " ++ (show lv) ++ "\nLocation type state: " ++ (show lts) ++ "\n"

-- | The type checking monad. Just for throwing errors, but could in the future be parameterized
--   by whatever other logging, etc, monad we want the compiler to use.
type TcM a = (Except TCError) a



-- | Check an expression. Given the data definitions, an general type environment, a function map,
--   a constraint set, a region set, an (input) location state map, and the expression, this function
--   will either throw an error, or return a pair of expression type and new location state map.
tcExp :: DDefs Ty2 -> Env2 Ty2 -> FunDefs2
      -> ConstraintSet -> RegionSet -> LocationTypeState -> Exp
      -> TcM (Ty2, LocationTypeState)
tcExp ddfs env funs constrs regs tstatein exp =

    case exp of

      VarE v ->
          -- Look up a variable in the environment
          do ty <- lookupVar env v exp
             return (ty, tstatein)

      LitE _i -> return (IntTy, tstatein)

      FloatE _i -> return (FloatTy, tstatein)

      LitSymE _v -> return (SymTy, tstatein)

      AppE v ls args ->
          -- Checking function application involves a few steps:
          --  (1) We need to make sure the inputs/ouptuts line up with the expected
          --      types for the function.
          --  (2) We need to update the location state map with information about what output
          --      locations have been written to by the called function and must now be input
          --      locations.
          --  (3) We need to make sure that if we pass a packed structure as an argument, its
          --      location is among the passed-in locations.
          do let (ArrowTy2 locVars arrIns _arrEffs arrOut _locRets _isPar) =
                     case M.lookup v funs of
                       Just f -> funTy f
                       Nothing -> error $ "tcExp: Unbound function: " ++ sdoc v

             -- Get types of arguments
             (in_tys, tstate) <- foldlM
                                   (\(tys, st) a -> do
                                         (ty, st') <- recur st a
                                         pure (tys ++ [ty], st'))
                                   ([],tstatein) args

             -- Check arity
             if (length args) /= (length in_tys)
             then throwError $ GenericTC ("Arity mismatch. Expected:" ++ show (length in_tys) ++
                                          " Got:" ++ show (length args)) exp
             else pure ()

             -- (1)
             mapM (uncurry $ ensureEqualTyNoLoc exp) (fragileZip in_tys arrIns)

             -- (3) Check location of argument
             let tyls = concatMap locsInTy in_tys
             case find (\loc -> not $ S.member loc (S.fromList ls)) tyls of
               Nothing -> return ()
               Just not_in_ls -> throwError $ GenericTC ("Packed argument location expected: " ++ show not_in_ls) exp
             let handleTS ts (l,Output) =  switchOutLoc exp ts l
                 handleTS ts _ = return ts
             -- (2)
             tstate' <- foldM handleTS tstate $ zip ls $ L.map (\(LRM _ _ m) -> m) locVars
             -- Use locVars used at call-site in the returned type
             let arrOutMp = M.fromList $ zip (L.map (\(LRM l _ _) -> l) locVars) ls
                 arrOut'  = substLoc arrOutMp arrOut

             return (arrOut',tstate')

      PrimAppE pr es -> do
               -- Special case because we can't lookup the type of the function pointer
               let es' = case pr of
                           VSortP{} -> init es
                           InPlaceVSortP{} -> init es
                           _        -> es
               (tys,tstate) <- tcExps ddfs env funs constrs regs tstatein es'

               -- Pattern matches would be one way to check length safely, but then the
               -- error would not go through our monad:
               let len2 = checkLen exp pr 2 es
                   len1 = checkLen exp pr 1 es
                   len0 = checkLen exp pr 0 es
                   _len3 = checkLen exp pr 3 es
                   len4 = checkLen exp pr 4 es

                   mk_bools = do
                     len0
                     pure (BoolTy, tstate)

                   bool_ops = do
                     len2
                     _ <- ensureEqualTy (es !! 0) BoolTy (tys !! 0)
                     _ <- ensureEqualTy (es !! 1) BoolTy (tys !! 1)
                     pure (BoolTy, tstate)

                   int_ops = do
                     len2
                     _ <- ensureEqualTy (es !! 0) IntTy (tys !! 0)
                     _ <- ensureEqualTy (es !! 1) IntTy (tys !! 1)
                     pure (IntTy, tstate)

                   float_ops = do
                     len2
                     _ <- ensureEqualTy (es !! 0) FloatTy (tys !! 0)
                     _ <- ensureEqualTy (es !! 1) FloatTy (tys !! 1)
                     pure (FloatTy, tstate)

                   int_cmps = do
                     len2
                     _ <- ensureEqualTy (es !! 0) IntTy (tys !! 0)
                     _ <- ensureEqualTy (es !! 1) IntTy (tys !! 1)
                     pure (BoolTy, tstate)

                   float_cmps = do
                     len2
                     _ <- ensureEqualTy (es !! 0) FloatTy (tys !! 0)
                     _ <- ensureEqualTy (es !! 1) FloatTy (tys !! 1)
                     pure (BoolTy, tstate)

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

                 RandP -> return (IntTy, tstate)
                 FRandP -> return (FloatTy, tstate)

                 FloatToIntP -> do
                   len1
                   ensureEqualTy exp FloatTy (tys !! 0)
                   return (IntTy, tstate)

                 IntToFloatP -> do
                   len1
                   ensureEqualTy exp IntTy (tys !! 0)
                   return (FloatTy, tstate)

                 FSqrtP -> do
                   len1
                   ensureEqualTy exp FloatTy (tys !! 0)
                   return (FloatTy, tstate)

                 Gensym -> len0 >>= \_ -> pure (SymTy, tstate)

                 EqSymP -> do
                   len2
                   ensureEqualTy exp SymTy (tys !! 0)
                   ensureEqualTy exp SymTy (tys !! 1)
                   return (BoolTy,tstate)

                 SymAppend  -> do
                   len2
                   _ <- ensureEqualTy (es !! 0) SymTy (tys !! 0)
                   _ <- ensureEqualTy (es !! 1) IntTy (tys !! 1)
                   return (SymTy, tstate)

                 DictEmptyP ty -> do
                   len1
                   let [a] = tys
                   _ <- ensureEqualTy exp ArenaTy a
                   case es !! 0 of
                     (VarE var) ->
                         do ensureArenaScope exp env (Just var)
                            return (SymDictTy (Just var) (stripTyLocs ty), tstate)
                     _ -> throwError $ GenericTC "Expected arena variable argument" exp

                 DictInsertP ty -> do
                   len4
                   let [a,d,k,v]  = tys
                   _ <- ensureEqualTy exp ArenaTy a
                   _ <- ensureEqualTy exp SymTy k
                   _ <- ensureEqualTyNoLoc exp ty v
                   case d of
                     SymDictTy ar _ty ->
                         case es !! 0 of
                           (VarE var) ->
                               do ensureArenaScope exp env ar
                                  ensureArenaScope exp env (Just var)
                                  return (SymDictTy (Just var) (stripTyLocs ty), tstate)
                           _ -> throwError $ GenericTC "Expected arena variable argument" exp
                     _ -> throwError $ GenericTC "Expected SymDictTy" exp

                 DictLookupP ty -> do
                   len2
                   let [d,k]  = tys
                   case d of
                     SymDictTy ar _ty ->
                         do _ <- ensureEqualTy exp SymTy k
                            ensureArenaScope exp env ar
                            return (ty, tstate)
                     _ -> throwError $ GenericTC "Expected SymDictTy" exp

                 DictHasKeyP _ty -> do
                   len2
                   let [d,k]  = tys
                   case d of
                     SymDictTy ar _ty -> do _ <- ensureEqualTy exp SymTy k
                                            ensureArenaScope exp env ar
                                            return (BoolTy, tstate)
                     _ -> throwError $ GenericTC "Expected SymDictTy" exp

                 SizeParam -> do
                   len0
                   return (IntTy, tstate)

                 IsBig -> do
                   len2
                   let [ity, ety] = tys
                   ensureEqualTy exp ity IntTy
                   if isPackedTy ety
                   then pure (BoolTy, tstate)
                   else error "L1.Typecheck: IsBig expects a Packed value."

                 ErrorP _str ty -> do
                   len0
                   return (ty, tstate)

                 ReadPackedFile _fp _tycon _reg ty -> do
                   len0
                   return (ty, tstate)

                 ReadArrayFile _ ty -> do
                   len0
                   if isValidListElemTy ty
                   then return (VectorTy ty, tstate)
                   else throwError $ GenericTC "Not a valid list type" exp

                 RequestEndOf -> do
                   len1
                   case (es !! 0) of
                     VarE{} -> if isPackedTy (tys !! 0)
                               then return (CursorTy, tstate)
                               else case (tys !! 0) of
                                      SymTy -> return (CursorTy, tstate)
                                      IntTy -> return (CursorTy, tstate)
                                      _ -> throwError $ GenericTC "Expected PackedTy" exp
                     -- L _ LitSymE{} -> return (CursorTy, tstate)
                     -- L _ LitE{} -> return (CursorTy, tstate)
                     _ -> throwError $ GenericTC "Expected a variable argument" exp

                 RequestSizeOf -> do
                   len1
                   case (es !! 0) of
                     VarE{} -> if isPackedTy (tys !! 0)
                               then return (IntTy, tstate)
                               else case (tys !! 0) of
                                      SymTy -> return (IntTy, tstate)
                                      IntTy -> return (IntTy, tstate)
                                      _ -> throwError $ GenericTC "Expected PackedTy" exp
                     _ -> throwError $ GenericTC "Expected a variable argument" exp

                 VEmptyP ty  -> do
                   len0
                   pure (VectorTy ty, tstate)
                 VNthP ty    -> do
                   let [i,ls] = tys
                   _ <- ensureEqualTy exp IntTy i
                   _ <- ensureEqualTy exp (VectorTy ty) ls
                   pure (ty, tstate)
                 VLengthP ty -> do
                   let [ls] = tys
                   _ <- ensureEqualTy exp (VectorTy ty) ls
                   pure (IntTy, tstate)
                 VUpdateP ty -> do
                   let [ls,i,val] = tys
                   _ <- ensureEqualTy exp (VectorTy ty) ls
                   _ <- ensureEqualTy exp IntTy i
                   _ <- ensureEqualTy exp ty val
                   pure (VectorTy ty, tstate)
                 VSnocP ty   -> do
                   let [ls,val] = tys
                   _ <- ensureEqualTy exp (VectorTy ty) ls
                   _ <- ensureEqualTy exp ty val
                   pure (VectorTy ty, tstate)

                 InPlaceVSnocP ty -> do
                    recur tstatein (PrimAppE (VSnocP ty) es)

                 -- Given that the first argument is a list of type (VectorTy t),
                 -- ensure that the 2nd argument is function reference of type:
                 -- ty -> ty -> Bool
                 VSortP ty ->
                   case (es !! 1) of
                     VarE f -> do
                       len2
                       let [ls]   = tys
                           fn_ty  = lookupFEnv f env
                           in_tys = inTys fn_ty
                           ret_ty = outTy fn_ty
                           err x  = throwError $ GenericTC ("vsort: Expected a sort function of type (ty -> ty -> Bool). Got"++ sdoc x) exp
                       _ <- ensureEqualTy (es !! 0) (VectorTy ty) ls
                       case in_tys of
                         [a,b] -> do
                            _ <- ensureEqualTy (es !! 1) a ty
                            _ <- ensureEqualTy (es !! 1) b ty
                            _ <- ensureEqualTy (es !! 1) ret_ty IntTy
                            pure (VectorTy ty, tstate)
                         _ -> err fn_ty
                     oth -> throwError $ GenericTC ("vsort: function pointer has to be a variable reference. Got"++ sdoc oth) exp

                 InPlaceVSortP ty -> do
                    recur tstatein (PrimAppE (VSortP ty) es)

                 VSliceP ty   -> do
                   let [ls,from,to] = tys
                   _ <- ensureEqualTy exp (VectorTy ty) ls
                   _ <- ensureEqualTy exp IntTy from
                   _ <- ensureEqualTy exp IntTy to
                   pure (VectorTy ty, tstate)

                 PrintInt -> throwError $ GenericTC "PrintInt not handled" exp
                 PrintSym -> throwError $ GenericTC "PrintSym not handled" exp
                 ReadInt  -> throwError $ GenericTC "ReadInt not handled" exp
                 SymSetEmpty -> throwError $ GenericTC "SymSetEmpty not handled" exp
                 SymSetInsert -> throwError $ GenericTC "SymSetInsert not handled" exp
                 SymSetContains -> throwError $ GenericTC "SymSetContains not handled" exp
                 SymHashEmpty -> throwError $ GenericTC "SymHashEmpty not handled" exp
                 SymHashInsert -> throwError $ GenericTC "SymHashInsert not handled" exp
                 SymHashLookup -> throwError $ GenericTC "SymHashLookup not handled" exp
                 IntHashEmpty -> throwError $ GenericTC "IntHashEmpty not handled" exp
                 IntHashInsert -> throwError $ GenericTC "IntHashInsert not handled" exp
                 IntHashLookup -> throwError $ GenericTC "IntHashLookup not handled" exp


      LetE (v,_ls,ty,e1) e2 -> do

               -- We get the type and new location state from e1
               (ty1,tstate1) <- recur tstatein e1
               ensureEqualTyNoLoc exp ty1 ty
               let env' = extendVEnv v ty env

               -- Then we check e1 with that location state
               tcExp ddfs env' funs constrs regs tstate1 e2

      IfE e1 e2 e3 -> do

               -- Handle condition
               (ty1,tstate1) <- recur tstatein e1
               ensureEqualTyModCursor exp ty1 BoolTy

               -- Check both branches
               (ty2,tstate2) <- recur tstate1 e2
               (ty3,tstate3) <- recur tstate1 e3

               -- Combine the type states somehow (TODO: audit this)
               tstate <- combineTStates exp tstate2 tstate3

               ensureEqualTyModCursor exp ty2 ty3
               return (ty2,tstate)

      MkProdE es -> do
               (tys,tstate) <- tcExps ddfs env funs constrs regs tstatein es
               return (ProdTy tys,tstate)

      ProjE i e -> do

               (ty,tstate) <- recur tstatein e
               tyi <- tcProj exp i ty
               return (tyi, tstate)

      CaseE e brs -> do

               (ty,tstate) <- recur tstatein e
               case ty of
                 PackedTy _dc lin -> do
                         -- We need to know the "region" of all the vars (and locations) pattern matched by this case expresssion.
                         -- The "region" is the same as that of the case scrutinee.
                         reg <- getRegion e constrs lin
                         ensureMatchCases ddfs exp ty brs
                         (tys,tstate') <- tcCases ddfs env funs constrs regs tstate lin reg brs
                         foldM_ (ensureEqualTyModCursor exp) (tys !! 0) (tail tys)
                         return (tys !! 0,tstate')
                 _ -> error ("Expected packed type, got " ++ show ty)

      DataConE l dc es -> do
               let dcty = getTyOfDataCon ddfs dc
               (tys,tstate1) <- tcExps ddfs env funs constrs regs tstatein es
               let args = lookupDataCon ddfs dc

               if length args /= length es
               then throwError $ GenericTC "Invalid argument length" exp
               else do
                 sequence_ [ ensureEqualTyNoLoc exp ty1 ty2
                           | (ty1,ty2) <- zip args tys ]
                 -- TODO: need to fix this check
                 -- ensureDataCon exp l tys constrs
                 tstate2 <- switchOutLoc exp tstate1 l
                 return (PackedTy dcty l, tstate2)

      TimeIt e _ty _b -> do

               (ty1,tstate1) <- recur tstatein e
               -- ensureEqualTy exp ty ty1
               return (ty1,tstate1)

      SpawnE f locs args ->
        tcExp ddfs env funs constrs regs tstatein (AppE f locs args)

      SyncE -> pure (ProdTy [], tstatein)

      WithArenaE v e -> do
              let env' = extendVEnv v ArenaTy env
              tcExp ddfs env' funs constrs regs tstatein e

      MapE _ _ -> throwError $ UnsupportedExpTC exp

      FoldE _ _ _ -> throwError $ UnsupportedExpTC exp

      Ext (LetRegionE r e) -> do

               regs' <- regionInsert exp r regs
               (ty,tstate) <- tcExp ddfs env funs constrs regs' tstatein e
               return (ty,tstate)

      Ext (LetLocE v c e) -> do
              let env' = extendVEnv v CursorTy env
              case c of
                StartOfLE r ->
                    do ensureRegion exp r regs
                       absentStart exp constrs r
                       let tstate1 = extendTS v (Output,False) tstatein
                       let constrs1 = extendConstrs (StartOfC v r) $ extendConstrs (InRegionC v r) constrs
                       (ty,tstate2) <- tcExp ddfs env' funs constrs1 regs tstate1 e
                       tstate3 <- removeLoc exp tstate2 v
                       return (ty,tstate3)
                AfterConstantLE i l1 ->
                     do r <- getRegion exp constrs l1
                        let tstate1 = extendTS v (Output,True) $ setAfter l1 tstatein
                        let constrs1 = extendConstrs (InRegionC v r) $ extendConstrs (AfterConstantC i l1 v) constrs
                        (ty,tstate2) <- tcExp ddfs env' funs constrs1 regs tstate1 e
                        tstate3 <- removeLoc exp tstate2 v
                        return (ty,tstate3)
                AfterVariableLE x l1 _ ->
                    do r <- getRegion exp constrs l1
                       (_xty,tstate1) <- tcExp ddfs env funs constrs regs tstatein $ VarE x
                       -- NOTE: We now allow aliases (offsets) from scalar vars too. So we can leave out this check
                       -- ensurePackedLoc exp xty l1
                       let tstate2 = extendTS v (Output,True) $ setAfter l1 tstate1
                       let constrs1 = extendConstrs (InRegionC v r) $ extendConstrs (AfterVariableC x l1 v) constrs
                       (ty,tstate3) <- tcExp ddfs env' funs constrs1 regs tstate2 e
                       tstate4 <- removeLoc exp tstate3 v
                       return (ty,tstate4)
                FromEndLE _l1 ->
                    do -- TODO: This is the bare minimum which gets the examples typechecking again.
                       -- Need to figure out if we need to check more things here
                      (ty,tstate1) <- tcExp ddfs env' funs constrs regs tstatein e
                      return (ty,tstate1)
                FreeLE ->
                    do let constrs1 = extendConstrs (InRegionC v globalReg) $ constrs
                       (ty,tstate1) <- tcExp ddfs env' funs constrs1 regs tstatein e
                       return (ty,tstate1)
                _ -> throwError $ GenericTC "Invalid letloc form" exp

      Ext (FromEndE{}) -> throwError $ GenericTC "FromEndE not handled" exp
      Ext (AddFixed{}) -> throwError $ GenericTC "AddFixed not handled" exp

      Ext (RetE _ls v) -> do

               -- skip returned locations for now
               recur tstatein $ VarE v

      -- The IntTy is just a placeholder. BoundsCheck is a side-effect
      Ext (BoundsCheck{}) -> return (IntTy,tstatein)

      Ext (IndirectionE tycon _ (a,_) _ _) -> return (PackedTy tycon a, tstatein)

      Ext GetCilkWorkerNum -> return (IntTy, tstatein)

      Ext (LetAvail _ e) -> recur tstatein e

    where recur ts e = tcExp ddfs env funs constrs regs ts e



-- | Helper function to check case branches.
tcCases :: DDefs Ty2 -> Env2 Ty2 -> FunDefs2
        -> ConstraintSet -> RegionSet -> LocationTypeState -> LocVar
        -> Region -> [(DataCon, [(Var,LocVar)], Exp)]
        -> TcM ([Ty2], LocationTypeState)
tcCases ddfs env funs constrs regs tstatein lin reg ((dc, vs, e):cases) = do

  let argtys = zip vs $ lookupDataCon ddfs dc
      pairwise = zip argtys $ Nothing : (L.map Just argtys)

      -- Generate the new constraints to check this branch
      genConstrs (((_v1,l1),PackedTy _ _),Nothing) (lin,lst) =
          (l1,[AfterConstantC 1 lin l1, InRegionC l1 reg] ++ lst)
      genConstrs (((_v1,l1),PackedTy _ _),Just ((v2,l2),PackedTy _ _)) (_lin,lst) =
          (l1,[AfterVariableC v2 l2 l1, InRegionC l1 reg] ++ lst)
      genConstrs (((_v1,l1),PackedTy _ _),Just ((_v2,_l2),IntTy)) (lin,lst) =
        let sz = fromMaybe 1 (sizeOfTy IntTy)
        in (l1, [AfterConstantC sz lin l1, InRegionC l1 reg] ++ lst)
      genConstrs (((_,l1),_),_) (lin,lst) =
        (lin, (InRegionC l1 reg : lst))

      -- Generate the new location state map to check this branch
      genTS ((_v,l),PackedTy _ _) ts = extendTS l (Input,False) ts
      genTS _ ts = ts
      genEnv ((v,l),PackedTy dc _l') env = extendVEnv v (PackedTy dc l) env
      genEnv ((v,_l),ty) env = extendVEnv v ty env

      -- Remove the pattern-bound location variables from the location state map
      remTS ((_v,l),PackedTy _ _) ts = removeTS l ts
      remTS _ ts = ts

      -- Use these functions with our old friend foldr
      constrs1 = L.foldr extendConstrs constrs $ snd $ L.foldr genConstrs (lin,[]) pairwise
      tstate1 = L.foldr genTS tstatein argtys
      env1 = L.foldr genEnv env argtys

  (ty1,tstate2) <- tcExp ddfs env1 funs constrs1 regs tstate1 e
  (tyRest,tstateRest) <- recur
  tstateCombine <- combineTStates e tstate2 tstateRest
  let tstatee' = L.foldr remTS tstateCombine argtys
  return (ty1:tyRest,tstatee')

    where recur = do
            (tys,tstate2) <- tcCases ddfs env funs constrs regs tstatein lin reg cases
            return (tys,tstate2)

tcCases _ _ _ _ _ ts _ _ [] = return ([],ts)

tcProj :: Exp -> Int -> Ty2 -> TcM Ty2
tcProj _ i (ProdTy tys) = return $ tys !! i
tcProj e _i ty = throwError $ GenericTC ("Projection from non-tuple type " ++ (show ty)) e

-- | A wrapper for tcExp to check a list of exprs, checking them in order:
-- the order matters because the location state map is threaded through,
-- so this is assuming the list of expressions would have been evaluated
-- in first-to-last order.
tcExps :: DDefs Ty2 -> Env2 Ty2 -> FunDefs2
      -> ConstraintSet -> RegionSet -> LocationTypeState -> [Exp]
      -> TcM ([Ty2], LocationTypeState)
tcExps ddfs env funs constrs regs tstatein (exp:exps) =
    do (ty,ts) <- tcExp ddfs env funs constrs regs tstatein exp
       (tys,ts') <- tcExps ddfs env funs constrs regs ts exps
       return (ty:tys,ts')
tcExps _ _ _ _ _ ts [] = return ([],ts)



-- | Main entry point, checks a whole program (functions and main body).
tcProg :: Prog2 -> PassM Prog2
tcProg prg0@Prog{ddefs,fundefs,mainExp} = do

  -- Handle functions
  mapM_ fd $ M.elems fundefs

  -- Handle main function
  case mainExp of
    Nothing -> return ()
    Just (e,t) ->
        let init_env = progToEnv prg0
            res = runExcept $ tcExp ddefs init_env fundefs
                    (ConstraintSet $ S.empty) (RegionSet $ S.empty)
                    (LocationTypeState $ M.empty) e
        in case res of
             Left err -> error $ show err
             Right (t',_ts) ->
                 if t' == t then return ()
                 else error $ "Expected type " ++ (show t) ++ " and got type " ++ (show t')

  return prg0 -- Identity function for now.

  where

    fd :: FunDef2 -> PassM ()
    fd func@FunDef{funTy,funArgs,funBody} = do
        let init_env = progToEnv prg0
            env = extendsVEnv (M.fromList $ zip funArgs (arrIns funTy)) init_env
            constrs = funConstrs (locVars funTy)
            regs = funRegs (locVars funTy)
            tstate = funTState (locVars funTy)
            res = runExcept $ tcExp ddefs env fundefs constrs regs tstate funBody
        case res of
          Left err -> error $ show err
          Right (ty,_) -> if ty == (arrOut funTy)
                          then return ()
                          else error $ "Expected type " ++ (sdoc (arrOut funTy))
                                    ++ " and got type " ++ (sdoc ty)
                                    ++ " in\n" ++ (sdoc func)



--------------------------------------------------------------------------------------------

-- Helper functions


-- | Insert a region into a region set.
-- Includes an expression for error reporting.
regionInsert :: Exp -> Region -> RegionSet -> TcM RegionSet
regionInsert e r (RegionSet regSet) = do
  if (S.member (regionToVar r) regSet)
  then throwError $ GenericTC "Shadowed regions not allowed" e
  else return $ RegionSet (S.insert (regionToVar r) regSet)

-- | Ask if a region is in the region set.
hasRegion :: Region -> RegionSet -> Bool
hasRegion r (RegionSet regSet) = S.member (regionToVar r) regSet

-- | Ensure that a region is in a region set, reporting an error otherwise.
-- Includes an expression for error reporting.
ensureRegion :: Exp -> Region -> RegionSet -> TcM ()
ensureRegion exp r (RegionSet regSet) =
    if S.member (regionToVar r) regSet then return ()
    else throwError $ GenericTC ("Region " ++ (show r) ++ " not in scope") exp

-- | Get the region of a location variable.
-- Includes an expression for error reporting.
getRegion :: Exp -> ConstraintSet -> LocVar -> TcM Region
getRegion exp (ConstraintSet cs) l = go $ S.toList cs
    where go ((InRegionC l1 r):cs) = if l1 == l then return r
                                     else go cs
          go (_:cs) = go cs
          go [] = throwError $ GenericTC ("Location " ++ (show l) ++ " has no region") exp

-- | Get the regions mentioned in the location bindings in a function type.
funRegs :: [LRM] -> RegionSet
funRegs ((LRM _l r _m):lrms) =
    let (RegionSet rs) = funRegs lrms
    in RegionSet $ S.insert (regionToVar r) rs
funRegs [] = RegionSet $ S.empty

globalReg :: Region
globalReg = GlobR "GLOBAL" BigInfinite

-- | Get the constraints from the location bindings in a function type.
funConstrs :: [LRM] -> ConstraintSet
funConstrs ((LRM l r _m):lrms) =
    extendConstrs (InRegionC l r) $ funConstrs lrms
funConstrs [] = ConstraintSet $ S.empty

-- | Get the type state implied by the location bindings in a function type.
funTState :: [LRM] -> LocationTypeState
funTState ((LRM l _r m):lrms) =
    extendTS l (m,False) $ funTState lrms
funTState [] = LocationTypeState $ M.empty

-- | Look up the type of a variable from the environment
-- Includes an expression for error reporting.
lookupVar :: Env2 Ty2 -> Var -> Exp -> TcM Ty2
lookupVar env var exp =
    case M.lookup var $ vEnv env of
      Nothing -> throwError $ VarNotFoundTC var exp
      Just ty -> return ty

-- | Combine two location state maps.
-- Currently just uses a naive union, which will not verify that different branches do the same
-- things.
-- TODO: Fix this!
combineTStates :: Exp -> LocationTypeState -> LocationTypeState -> TcM LocationTypeState
combineTStates _exp (LocationTypeState ts1) (LocationTypeState ts2) =
    return $ LocationTypeState $ M.union ts1 ts2
    -- throwError $ DivergingEffectsTC exp ts1 ts2

-- | Ensure that two things are equal.
-- Includes an expression for error reporting.
ensureEqual :: Eq a => Exp -> String -> a -> a -> TcM a
ensureEqual exp str a b = if a == b then return a else throwError $ GenericTC str exp

-- | Ensure that the number of arguments to an operation is correct.
checkLen :: (Show op, Show arg) => Exp -> op -> Int -> [arg] -> TcM ()
checkLen expr pr n ls =
  if length ls == n
  then return ()
  else throwError $ GenericTC ("Wrong number of arguments to "++show pr++
                               ".\nExpected "++show n++", received "
                                ++show (length ls)++":\n  "++show ls) expr

-- | Ensure that two types are equal.
-- Includes an expression for error reporting.
ensureEqualTy :: Exp -> Ty2 -> Ty2 -> TcM Ty2
ensureEqualTy exp a b = ensureEqual exp ("Expected these types to be the same: "
                                         ++ (show a) ++ ", " ++ (show b)) a b

ensureEqualTyModCursor :: Exp -> Ty2 -> Ty2 -> TcM Ty2
ensureEqualTyModCursor _exp CursorTy (PackedTy _ _) = return CursorTy
ensureEqualTyModCursor _exp (PackedTy _ _) CursorTy = return CursorTy
ensureEqualTyModCursor exp a b = ensureEqualTy exp a b

-- | Ensure that two types are equal, ignoring the locations if they are packed.
-- Includes an expression for error reporting.
ensureEqualTyNoLoc :: Exp -> Ty2 -> Ty2 -> TcM Ty2
ensureEqualTyNoLoc exp ty1 ty2 =
  case (ty1,ty2) of
    (SymDictTy _ar1 ty1, SymDictTy _ar2 ty2) ->
        do ty1' <- dummyTyLocs ty1
           ty2' <- dummyTyLocs ty2
           ensureEqualTyNoLoc exp ty1' ty2'
    (PackedTy dc1 _, PackedTy dc2 _) -> if dc1 == dc2
                                        then return ty1
                                        else ensureEqualTy exp ty1 ty2
    (ProdTy tys1, ProdTy tys2) -> do
        checks <- return $ L.map (\(ty1,ty2) -> ensureEqualTyNoLoc exp ty1 ty2) (zip tys1 tys2)
        -- TODO: avoid runExcept here
        forM_ checks $ \c -> do
            let c' = runExcept c
            case c' of
              Left err -> throwError err
              Right _  -> return ()
        return ty1
    _ -> ensureEqualTyModCursor exp ty1 ty2


-- | Ensure that match cases make sense.
-- Includes an expression for error reporting.
ensureMatchCases :: DDefs Ty2 -> Exp -> Ty2 -> [(DataCon, [(Var,LocVar)], Exp)] -> TcM ()
ensureMatchCases ddfs exp ty cs = do
  case ty of
    PackedTy tc _l -> do
            let cons = S.fromList $ L.map fst $ dataCons $ lookupDDef ddfs tc
            forM cs $ \(dc,_,_) ->
                do if S.member dc cons
                   then return ()
                   else throwError $ GenericTC "Invalid case statement" exp
            return ()
    _ -> throwError $ GenericTC "Cannot case on non-packed type" exp

-- | Ensure a type is at a particular location.
-- Includes an expression for error reporting.
ensurePackedLoc :: Exp -> Ty2 -> LocVar -> TcM ()
ensurePackedLoc exp ty l =
    case ty of
      PackedTy _ l1 -> if l1 == l then return ()
                       else throwError $ GenericTC ("Wrong location in type " ++ (show ty)) exp
      _ -> throwError $ GenericTC "Expected a packed type" exp

-- need to check chain of aliased locations
-- linit is the location in the type i.e lout653
-- ensureAfterConstant expects l664 to be after lout653

-- | Ensure the locations all line up with the constraints in a data constructor application.
-- Includes an expression for error reporting.
ensureDataCon :: Exp -> LocVar -> [Ty2] -> ConstraintSet -> TcM ()
ensureDataCon exp linit tys cs = trace (sdoc cs) (go Nothing linit tys)
    where go Nothing linit ((PackedTy dc l):tys) = do
            ensureAfterConstant exp cs linit l
            go (Just (PackedTy dc l)) l tys

          go Nothing linit (_ty:tys) = go Nothing linit tys

          go (Just (PackedTy _dc1 l1)) _linit ((PackedTy dc2 l2):tys) = do
            ensureAfterPacked exp cs l1 l2
            go (Just (PackedTy dc2 l2)) l2 tys

          go (Just (PackedTy _dc _l1)) linit (_ty:tys) =
              go Nothing linit tys
          go _ _ [] = return ()
          go _ _ _  = internalError "Unxpected case reached: L2:ensureDataCon"


-- | Ensure that one location is +c after another location in the constraint set.
-- Includes an expression for error reporting.
ensureAfterConstant :: Exp -> ConstraintSet -> LocVar -> LocVar -> TcM ()
ensureAfterConstant exp (ConstraintSet cs) l1 l2 =
    if L.any f $ S.toList cs then return ()
    else throwError $ LocationTC "Expected after constant relationship" exp l1 l2
    -- l1 is before l2
    where f (AfterConstantC _i l1' l2') = l1' == l1 && l2' == l2
          f _ = False

-- | Ensure that one location is a variable size after another location in the constraint set.
-- Includes an expression for error reporting.
ensureAfterPacked :: Exp -> ConstraintSet -> LocVar -> LocVar -> TcM ()
ensureAfterPacked  exp (ConstraintSet cs) l1 l2 =
    if L.any f $ S.toList cs then return ()
    else throwError $ LocationTC "Expected after packed relationship" exp l1 l2
    where f (AfterVariableC _v l1' l2') = l1' == l1 && l2' == l2
          f _ = False


extendTS
  :: LocVar
     -> (Modality, Aliased) -> LocationTypeState -> LocationTypeState
extendTS v d (LocationTypeState ls) = LocationTypeState $ M.insert v d ls

removeTS :: LocVar -> LocationTypeState -> LocationTypeState
removeTS l (LocationTypeState ls) = LocationTypeState $ M.delete l ls

setAfter :: LocVar -> LocationTypeState -> LocationTypeState
setAfter l (LocationTypeState ls) = LocationTypeState $ M.adjust (\(m,_) -> (m,True)) l ls

_lookupTS :: Exp -> LocVar -> LocationTypeState -> TcM (Modality,Bool)
_lookupTS exp l (LocationTypeState ls) =
    case M.lookup l ls of
      Nothing -> throwError $ GenericTC ("Failed lookup of location " ++ (show l)) exp
      Just d -> return d

extendConstrs :: LocConstraint -> ConstraintSet -> ConstraintSet
extendConstrs c (ConstraintSet cs) = ConstraintSet $ S.insert c cs

switchOutLoc :: Exp -> LocationTypeState -> LocVar -> TcM LocationTypeState
switchOutLoc exp (LocationTypeState ls) l =
    case M.lookup l ls of
      Nothing -> throwError $ GenericTC ("Unknown location " ++ (show l)) exp
      Just (Output,a) -> return $ LocationTypeState $ M.update (\_ -> Just (Input,a)) l ls
      Just (Input,_a) -> throwError $ ModalityTC "Expected output location" exp l $
                                      LocationTypeState ls

_absentAfter :: Exp -> LocationTypeState -> LocVar -> TcM ()
_absentAfter exp (LocationTypeState ls) l =
    case M.lookup l ls of
      Nothing -> throwError $ GenericTC ("Unknown location " ++ (show l)) exp
      Just (_m,False) -> return ()
      Just (_m,True) -> throwError $ GenericTC ("Alias of location " ++ (show l)) exp

-- | Ensure that a location is not already "defined" by a start constraint.
absentStart :: Exp -> ConstraintSet -> Region -> TcM ()
absentStart exp (ConstraintSet cs) r = go $ S.toList cs
    where go ((StartOfC _l r'):cs) =
              if r == r'
              then throwError $ GenericTC ("Repeated start of " ++ (show r)) exp
              else go cs
          go (_:cs) = go cs
          go [] = return ()


removeLoc :: Exp -> LocationTypeState -> LocVar -> TcM LocationTypeState
removeLoc exp (LocationTypeState ls) l =
    if M.member l ls
    then return $ LocationTypeState $ M.delete l ls
    else throwError $ GenericTC ("Cannot remove location " ++ (show l)) exp

ensureArenaScope :: MonadError TCError m => Exp -> Env2 a -> Maybe Var -> m ()
ensureArenaScope exp env ar =
    case ar of
      Nothing -> throwError $ GenericTC "Expected arena annotation" exp
      Just var -> unless (S.member var . M.keysSet . vEnv $ env) $
                  throwError $ GenericTC ("Expected arena in scope: " ++ sdoc var) exp
