{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unused-local-binds  #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
{-# HLINT ignore "Use if" #-}
{-# HLINT ignore "Move brackets to avoid $" #-}
{-# HLINT ignore "Redundant <$>" #-}
module Gibbon.Passes.Cursorize
  (cursorize) where

import Control.Monad (forM)
import Data.Foldable (foldlM, foldrM)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Mb
import Data.Maybe (fromJust)
import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.L3.Syntax hiding
  ( AllocateScalarsHere,
    AllocateTagHere,
    BoundsCheck,
    GetCilkWorkerNum,
    LetAvail,
    RetE,
    SSPop,
    SSPush,
    TagCursor,
  )
import qualified Gibbon.L3.Syntax as L3
import qualified Gibbon.L2.Syntax as L2
import Gibbon.NewL2.Syntax
import Gibbon.Passes.AddRAN (numRANsDataCon)
import GHC.Stack (CallStack, HasCallStack, callStack, getCallStack, srcLocFile, srcLocStartCol, srcLocStartLine)
import Text.PrettyPrint.GenericPretty
import Gibbon.L2.Syntax (EndRegionModality)

{-

Cursor insertion, strategy one:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Here we go to a "dilated" representation of packed values, where
every `Packed T` is represented by a pair, `(Cursor,Cursor)`,
i.e. start/end. Except function arguments, and variables bound by
by a pattern match. They're just `start` cursors.

REASONING: Why the dilated convention?  In a word: conditionals.  At the
end of each function body we need to return the appropriate end cursors.
But during the computation, we may need to add an arbitrary amount of
extra state to the return type of a conditional.  Thus it's difficult to
do this routing of information without changing the types of intermediate
expressions significantly.  Dilation is the current strategy.

We proceed with two loops, corresponding to packed and unpacked
context.  When the type of the current expression satisfies
`hasPacked`, that's when we're in packed context.  And, when in
packed context, we return dilated values.

E.g.

    type Tree = Leaf Int | Node Tree Tree

    add1 :: Tree -> Tree
    add1 tr =
      case tr of
        Leaf n   -> Leaf (n + 1)
        Node l r -> Node (add1 l) (add1 r)

becomes

    -- char*
    type Cursor = Ptr Char

    add1 :: Cursor -> Cursor -> (Cursor, (Cursor, Cursor))
    add1 lout lin =
      let tag = readTag lin
      in case tag of
           Leaf -> let n  = readInt tag
                       wt = writeTag lout Leaf
                       wi = writeInt wt   (n+1)
                   in (lin + 8, (lout, wi))
           Node -> ...


----------------------------------------------------------------------
For enabling tail recursion, we need mutable cursors. 
The function return value is gone, we are just left with the arguments.
type MutCursor = Ptr Ptr Char
add1 :: MutCursor -> Cursor -> ()
add1 lout lin = 
  let tag = readTag lin 
   in case tag of 
        Leaf  -> let n = readInt (tag + 1) 
                     () = writeTagMutable lout Leaf
                     () = BumpMutableCursor lout 1  
                     () = writeIntMutable lout (n+1)
                     () = BumpMutableCursor lout 8
                   in ()
        Node -> ...

-- For the SoA transformation, the add1 function would look something like 
-- the following 
-- The arrays are already references 
-- only MutCursors will be needed in the body
-- Both input and output are Mutable here.
add1 :: CursorArray[2] -> CursorArray[2] -> ()
add1 lout lin =
  let tagloc = lin[0]
      leafloc = lin[1]
      taglocout = lout[0]
      leaflocout = lout[1]
      tag = readTagMutable tagloc
      () = BumpMutableCursor tagloc 1
   in case tag of
        Leaf  -> let n = readIntMutable (leafloc)
                     () = BumpMutableCursor leafloc 8
                     () = writeTagMutable taglocout Leaf
                     () = BumpMutableCursor taglocout 1
                     () = writeIntMutable leaflocout (n+1)
                     () = BumpMutableCursor leaflocout 8
                   in ()
        Node -> let
                  () = writeTagMutable taglocout Node
                  () = BumpMutableCursor taglocout 1
                  () = add1 lout lin
                  () = add1 lout lin
                 in ()



Every packed input becomes a read cursor. And it takes additional output cursors
for every packed type in the return value. Every packed return value becomes a
(Cursor,Cursor) i.e (start,end). And it returns additional end_of_read cursors
if the functions "traverses" it's input (more details in the paer).

    [VS]
    -- SoA representation
    -- char*
    type Cursor = Ptr Char
    type CursorArray_${Int} = Cursor[Int]

    CursorArray_2 = {Cursor, Cursor}
      where:
        CursorArray_2[0] = tag buffer cursor
        CursorArray_2[1] = integer buffer cursor (Leaf)

    add1 :: CursorArray_2 -> CursorArray_2 -> (CursorArray_2, (CursorArray_2, CursorArray_2))
    add1 lout lin =
      let tag = readTag lin[0]
      in case tag of
           Leaf -> let n  = readInt lin[1]
                       wt = writeTag lout[0] Leaf
                       wi = writeInt lout[1] (n+1)
                   in ({lin[0] + 1, lin[1] + 8}, (lout, {lout[0] + 1, lout[1] + 8}))
           Node -> ...
-}

-- | Track variables depending on location variables.
--
--   If we have to create binding of the form `let v = loc` (in case expressions for example),
--   but `loc` is not bound yet, we'll add the variable to this map.
--   This is a stupid/simple way to get rid of FindWitnesses.
--   See `FindWitnesses.hs` for why that is needed.
-- For both locs and regions
type DepEnv = M.Map FreeVarsTy [(Var, [()], Ty3, Exp3)]

noDeadFieldElimMarkerKey :: FreeVarsTy
noDeadFieldElimMarkerKey = fromVarToFreeVarsTy "__cursorize_internal_no_dead_fields__"

markNoDeadFieldElim :: DepEnv -> DepEnv
markNoDeadFieldElim denv = M.insert noDeadFieldElimMarkerKey [] denv

isNoDeadFieldElim :: DepEnv -> Bool
isNoDeadFieldElim denv = M.member noDeadFieldElimMarkerKey denv

selectiveShareMarkerKey :: L2.SelectiveShareTarget -> FreeVarsTy
selectiveShareMarkerKey tgt =
  fromVarToFreeVarsTy . toVar $
    case tgt of
      L2.ShareDConBuffer ->
        "__cursorize_internal_selective_share_dcon__"
      L2.ShareScalarFieldBuffer dcon idx ->
        "__cursorize_internal_selective_share_"
          ++ dcon
          ++ "_"
          ++ show idx
          ++ "__"

enableSelectiveShare :: Var -> [L2.SelectiveShareTarget] -> DepEnv -> DepEnv
enableSelectiveShare src tgts denv =
  foldr
    (\tgt acc -> M.insert (selectiveShareMarkerKey tgt) [(src, [], CursorTy, VarE src)] acc)
    denv
    tgts

lookupSelectiveShareSource :: L2.SelectiveShareTarget -> DepEnv -> Maybe Var
lookupSelectiveShareSource tgt denv =
  case M.lookup (selectiveShareMarkerKey tgt) denv of
    Just ((src, _, _, _) : _) -> Just src
    _ -> Nothing

hasSelectiveShareEnabled :: DepEnv -> Bool
hasSelectiveShareEnabled denv =
  any
    (\key ->
        case key of
          V v -> "__cursorize_internal_selective_share_" `L.isPrefixOf` fromVar v
          _ -> False
    )
    (M.keys denv)

usesTraverseCall :: Exp2 -> Bool
usesTraverseCall = go
  where
    go ex = case ex of
      AppE f _ _ args -> L.isPrefixOf "_traverse_" (fromVar f) || any go args
      PrimAppE _ args -> any go args
      LetE (_, _, _, rhs) bod -> go rhs || go bod
      IfE a b c -> go a || go b || go c
      MkProdE ls -> any go ls
      ProjE _ e -> go e
      CaseE e brs -> go e || any (\(_, _, rhs) -> go rhs) brs
      DataConE _ _ args -> any go args
      TimeIt e _ _ -> go e
      SpawnE _ _ args -> any go args
      WithArenaE _ e -> go e
      Ext ext -> case ext of
        LetRegionE _ _ _ _ bod -> go bod
        LetParRegionE _ _ _ bod -> go bod
        LetLocE _ _ bod -> go bod
        IndirectionE _ _ _ _ e -> go e
        _ -> False
      _ -> False

-- | Collect variables mentioned in an expression subtree.
-- This is used to avoid repeatedly traversing the same `CaseE` body
-- when computing per-field liveness.
varsMentionedInExp :: Exp2 -> S.Set Var
varsMentionedInExp = go
  where
    go :: Exp2 -> S.Set Var
    go ex = case ex of
      VarE v -> S.singleton v
      LitE{} -> S.empty
      CharE{} -> S.empty
      FloatE{} -> S.empty
      LitSymE{} -> S.empty
      AppE _ _ _ args -> S.unions (map go args)
      PrimAppE _ args -> S.unions (map go args)
      LetE (_, _, _, rhs) bod -> go rhs `S.union` go bod
      IfE a b c -> go a `S.union` go b `S.union` go c
      MkProdE ls -> S.unions (map go ls)
      ProjE _ e -> go e
      CaseE scrt brs -> go scrt `S.union` S.unions [go rhs | (_, _, rhs) <- brs]
      DataConE _ _ args -> S.unions (map go args)
      TimeIt e _ _ -> go e
      SpawnE _ _ args -> S.unions (map go args)
      SyncE -> S.empty
      MapE (_, _, rhs) bod -> go rhs `S.union` go bod
      FoldE (_, _, r1) (_, _, r2) bod -> go r1 `S.union` go r2 `S.union` go bod
      WithArenaE _ e -> go e
      Ext ext -> case ext of
        L2.LetRegionE _ _ _ _ bod -> go bod
        L2.LetParRegionE _ _ _ bod -> go bod
        L2.LetLocE _ locexp bod -> gFreeVars locexp `S.union` go bod
        L2.LetRegE _ _ bod -> go bod
        L2.IndirectionE _ _ _ _ e -> go e
        L2.StartOfPkdCursor v -> S.singleton v
        L2.RetE _ v -> S.singleton v
        L2.AddFixed v _ -> S.singleton v
        L2.LetAvail _ bod -> go bod
        _ -> S.empty

-- | Things we cannot define until we see a join point. There's a Ty2 to so that
-- we can extend the environment.
type SyncEnv = M.Map Var [(Var, [()], Ty3, Ty2, Exp3)]

type OldTy2 = UrTy LocVar

data WindowIntoCursor = AoSWin Var | SoAWin Var [((DataCon, Int), Var)]

cursorize :: Prog2 -> PassM Prog3
cursorize Prog {ddefs, fundefs, mainExp} = do
  dflags <- getDynFlags
  let userRequestedMutableCursors = gopt Opt_UseMutableCursors dflags
  fns' <- mapM (cursorizeFunDef ddefs fundefs . snd) (M.toList fundefs)
  let fundefs' = M.fromList $ L.map (\f -> (funName f, f)) fns'
      ddefs' = M.map eraseLocMarkers ddefs

  {- VS: TODO: Ensure that the map passed to these functions contains the correct values, rn just passing empty maps -}
  -- Assuming that the main exp is not going to involve tail recursive calls. 
  -- However, I think if we are changing the function signature of function. 
  -- We need to do some additional work to save the appropriate variables before the call.
  mainExp' <- case mainExp of
    Nothing -> return Nothing
    Just (e, ty) -> do
      if hasPacked (unTy2 ty)
        then
          do 
            (e', _, _, _) <- cursorizePackedExp M.empty M.empty userRequestedMutableCursors False False M.empty M.empty ddefs fundefs M.empty M.empty M.empty e
            Just . (,stripTyLocs (unTy2 ty))
              <$> return (fromDi e')
        else
          do 
          (e', _, _, _) <- cursorizeExp M.empty M.empty userRequestedMutableCursors False False M.empty M.empty ddefs fundefs M.empty M.empty M.empty e
          Just . (,stripTyLocs (unTy2 ty))
            <$> return e'
  pure (Prog ddefs' fundefs' mainExp')

mangle :: [Var] -> Var
mangle vars = toVar $ "mangle" ++ (L.foldr (\v acc -> acc ++ "_" ++ (fromVar v)) "" vars)

mkMakeCursorArrayDbg :: HasCallStack => Var -> [Var] -> Exp3
mkMakeCursorArrayDbg assignedVar locVars =
  dbgTrace
    (minChatLvl)
    ("Print in MakeCursorArray at " ++ makeCursorArraySrcLoc callStack ++ ": ")
    ( dbgTrace
        (minChatLvl)
        (sdoc (assignedVar, locVars))
        ( dbgTrace
            (minChatLvl)
            "End printing in MakeCursorArray.\n"
            (Ext $ MakeCursorArray (length locVars) locVars)
        )
    )

makeCursorArraySrcLoc :: CallStack -> String
makeCursorArraySrcLoc cs =
  case getCallStack cs of
    (_, loc) : _ ->
      srcLocFile loc
        ++ ":"
        ++ show (srcLocStartLine loc)
        ++ ":"
        ++ show (srcLocStartCol loc)
    [] -> "<unknown>"


-- The LocVar here is the field location, which we need to generate code for.
-- (Int, Int) is the start and end locations of that field.
-- Lots of operations on cursor might need to change in case we are using mutable cursors 
-- For instance, MakeCusroArray may be irrelevant.
handleIndexingSoACursors :: TyEnv Var Ty2 -> Maybe (Var, LocArg) -> MutableLocPtsToEnv -> MutableLocOldValueEnv -> Bool -> (LocVar, Var) -> (Int, Int) -> LocVar -> M.Map FreeVarsTy Var -> PassM (Var, M.Map FreeVarsTy Var, [(Var, [()], Ty3, Exp3)], MutableLocPtsToEnv, MutableLocOldValueEnv, TyEnv Var Ty2)
handleIndexingSoACursors tenv mbvarlarg m1 m2 forceMutable (arrLoc, arrName) (start, end) locvar var_env = do
                                           let par_var = case (M.lookup (fromLocVarToFreeVarsTy locvar) var_env) of 
                                                                          Just v -> v 
                                                                          Nothing -> case locvar of 
                                                                                          Single l -> l 
                                                                                          SoA{} -> error "Expected variable name for parent array!"
                                           let is_mutable_soa_loc = M.member locvar m1
                                           case arrLoc of
                                                -- Vidush TODO, need to handle mutable cursors here
                                                Single{} -> case is_mutable_soa_loc of 
                                                                    True -> do 
                                                                            -- deref_var <- gensym "derefed_var"
                                                                            --  LocVar -> MutableLocOldValueEnv -> (Var, Maybe LocVar, Maybe RegVar, S.Set Var) -> Bool
                                                                            case mbvarlarg of 
                                                                                 Just (aliasvar, aliaslocarg) -> do 
                                                                                                                  let arrLocInsideCase = toLocVar aliaslocarg
                                                                                                                  let arrLocNameInsideCase = getVarNameFromFreeVar var_env (fromLocVarToFreeVarsTy arrLocInsideCase)
                                                                                                                  (m2', deref_bnd) <- updateMutableLocOldValueEnv arrLoc m2 (arrName, Just arrLoc, Nothing, S.fromList [arrLocNameInsideCase, arrLocNameInsideCase]) True
                                                                                                                  let deref_var = case deref_bnd of 
                                                                                                                                      [(v, _, _, _)] -> v
                                                                                                                                      [] -> arrName
                                                                                                                  let m1' = updateMutableLocPtsToEnv arrLoc m1 (arrName, Just arrLoc, Nothing, S.fromList [arrLocNameInsideCase, arrLocNameInsideCase, deref_var]) True
                                                                                                                  let tenv' = M.insert arrName (MkTy2 MutCursorTy) tenv
                                                                                                                  return (deref_var, var_env, [(arrName, [], MutCursorTy, Ext $ AddrOfCursor $ Ext $ IndexCursorArray par_var start)] ++ deref_bnd, m1', m2', tenv')
                                                                                 Nothing -> do
                                                                                              (m2', deref_bnd) <- updateMutableLocOldValueEnv arrLoc m2 (arrName, Just arrLoc, Nothing, S.empty) True
                                                                                              let deref_var = case deref_bnd of 
                                                                                                              [(v, _, _, _)] -> v
                                                                                                              [] -> arrName
                                                                                              let m1' = updateMutableLocPtsToEnv arrLoc m1 (arrName, Just arrLoc, Nothing, S.singleton deref_var) True
                                                                                              let tenv' = M.insert arrName (MkTy2 MutCursorTy) tenv
                                                                                              return (deref_var, var_env, [(arrName, [], MutCursorTy, Ext $ AddrOfCursor $ Ext $ IndexCursorArray par_var start)] ++ deref_bnd, m1', m2', tenv')
                                                                    False -> return (arrName, var_env, [(arrName, [], CursorTy, Ext $ IndexCursorArray par_var start)], m1, m2, M.insert arrName (MkTy2 CursorTy) tenv)
                                                SoA{} -> do
                                                         let linearized_locs = (linearizeLocVar locvar)
                                                         (vars, bnds, var_env') <- foldlM (\(v, b, env) (i, l) -> do
                                                                                      (lvar, fenv') <- case (M.lookup (fromLocVarToFreeVarsTy l) var_env) of
                                                                                                                         Just v -> return (v, env)
                                                                                                                         Nothing -> do
                                                                                                                                    new_var <- gensym "unpack"
                                                                                                                                    let env' = M.insert (fromLocVarToFreeVarsTy l) new_var env
                                                                                                                                    return (new_var, env')
                                                                                      pure $ (v ++ [lvar], b ++ [(lvar, [], CursorTy, Ext $ IndexCursorArray par_var i)], fenv')

                                                           
                                                                                    ) ([], [], var_env) (zip [start..end] (take (end - start) (drop start linearized_locs)) )
                                                         let make_cur_arr_let = [(arrName, [], getCursorizeTyFromLocVar Nothing forceMutable arrLoc, mkMakeCursorArrayDbg arrName vars)]
                                                         return (arrName, var_env, bnds ++ make_cur_arr_let, m1, m2, tenv)

handleIndexingSoARegCursors :: Bool -> (RegVar, Var) -> (Int, Int) -> RegVar -> M.Map FreeVarsTy Var -> PassM (M.Map FreeVarsTy Var, [(Var, [()], UrTy (), (PreExp E3Ext () (UrTy ())))])
handleIndexingSoARegCursors forceMutable (arrLoc, arrName) (start, end) locvar var_env = do
                                           let par_var = case (M.lookup (fromRegVarToFreeVarsTy locvar) var_env) of 
                                                                          Just v -> v 
                                                                          Nothing -> case locvar of 
                                                                                          SingleR l -> l 
                                                                                          SoARv{} -> error "Expected variable name for parent array!"
                                           case arrLoc of 
                                                SingleR{} -> do 
                                                            return (var_env, [(arrName, [], CursorTy, Ext $ IndexCursorArray par_var start)])
                                                SoARv{} -> do
                                                         let linearized_locs = (linearizeRegVar locvar)
                                                         (vars, bnds, var_env') <- foldlM (\(v, b, env) (i, l) -> do
                                                                                      (lvar, fenv') <- case (M.lookup (fromRegVarToFreeVarsTy l) var_env) of
                                                                                                                         Just v -> return (v, env)
                                                                                                                         Nothing -> do
                                                                                                                                    new_var <- gensym "unpack"
                                                                                                                                    let env' = M.insert (fromRegVarToFreeVarsTy l) new_var env
                                                                                                                                    return (new_var, env')
                                                                                      pure $ (v ++ [lvar], b ++ [(lvar, [], CursorTy, Ext $ IndexCursorArray par_var i)], fenv')

                                                           
                                                                                    ) ([], [], var_env) (zip [start..end] (take (end - start) (drop start linearized_locs)) )
                                                         let make_cur_arr_let = [(arrName, [], getCursorizeTyFromRegVar''' Nothing forceMutable arrLoc, mkMakeCursorArrayDbg arrName vars)]
                                                         return (var_env, bnds ++ make_cur_arr_let)


cursorizeFunDef :: DDefs Ty2 -> FunDefs2 -> FunDef2 -> PassM FunDef3
cursorizeFunDef ddefs fundefs FunDef {funName, funTy, funArgs, funBody, funMeta} = do
  dflags <- getDynFlags
  let userRequestedMutableCursors = gopt Opt_UseMutableCursors dflags
      storeScalarCounts =
        gopt Opt_StoreScalarFieldCounts dflags &&
        StoreScalarCounts `elem` funOpt funMeta
  let fmet@FunMeta{funRec} = funMeta
  let isFunRec = case funRec of 
                            TailRec -> True
                            Rec -> True 
                            _ -> False
  let hasPackedInput = any (hasPacked . unTy2) (arrIns funTy)
  let hasPackedOutput = hasPacked (unTy2 (arrOut funTy))
  -- Vidush: This is true if we mush optimize the function for tail recursion.
  -- && isFunTailRec
  let useMutableCursors = userRequestedMutableCursors && isFunRec && (hasPackedInput || hasPackedOutput)
  let inLocs = inLocVars funTy
      inLocA = inLocArgs funTy
      outLocs = outLocVars funTy
      outRegs = (outRegVars funTy) ++ (L2.outRegVarsMutable funTy) 
      inRegs = inRegVars funTy
      in_tys = arrIns funTy
      out_ty = arrOut funTy

      inLocsMutable = L2.inLocVarsMutable funTy 
      outLocsMutable = L2.outLocVarsMutable funTy

      funTy' = cursorizeArrowTy useMutableCursors funTy

      -- [2019.03.04] CSK: the order of these new cursor/region arguments isn't
      -- intuitive and can be improved.

      -- Input & output regions are always inserted before all other arguments.
      -- {- VS: adding toEndVRegVar may be useless -}
      regBinds = dbgTrace (minChatLvl) "Print funTy': " dbgTrace (minChatLvl) (sdoc (funTy')) dbgTrace (minChatLvl) "End printing in funTy'.\n" map toEndVRegVar (inRegs ++ outRegs)

      -- Output cursors after that.
      outCurBinds = outLocs

      freeVarToVarEnv = M.empty
      freeVarsInScope = (L.map fromLocVarToFreeVarsTy outCurBinds) ++ (L.map fromRegVarToFreeVarsTy regBinds) ++ (L.map fromVarToFreeVarsTy funArgs) ++ (L.map fromLocVarToFreeVarsTy inLocs)
  -- freeVarToVarEnv' = L.foldr (\fv acc -> case fv of
  --                                         V v -> M.insert fv v acc
  --                                         FL l -> case l of
  --                                                     Single loc -> M.insert fv loc acc
  --                                                     SoA _ _ -> let name = mangle (varsInLocVar l)
  --                                                                   in M.insert fv name acc
  --                                         R r -> case r of
  --                                                   SingleR v -> M.insert fv v acc
  --                                                   SoARv _ _ -> let name = mangle (varsInRegVar r)
  --                                                                 in M.insert fv name acc
  --                            ) freeVarToVarEnv freeVarsInScope

  freeVarToVarEnv' <-
    foldrM
      ( \fv acc -> do
          case fv of
            V v -> return $ M.insert fv v acc
            FL l -> case l of
              Single loc -> return $ M.insert fv loc acc
              SoA _ _ -> do
                name <- gensym "cursor_ptr"
                return $ M.insert fv name acc
            R r -> case r of
              SingleR v -> return $ M.insert fv v acc
              SoARv _ _ -> do
                name <- gensym "cursor_ptr"
                return $ M.insert fv name acc
      )
      freeVarToVarEnv
      freeVarsInScope

  let freeVarToVarEnv'' =
        foldr
          ( \(LRM l r _) acc ->
              let actualEndKey = fromRegVarToFreeVarsTy (toEndVRegVar (regionToVar r))
                  locEndKey = fromRegVarToFreeVarsTy (toEndVRegVar (fromLocVarToRegVar l))
               in case M.lookup actualEndKey acc of
                    Just v -> M.insert locEndKey v acc
                    Nothing -> acc
          )
          freeVarToVarEnv'
          (locVars funTy)

  -- Then the input cursors. Bind an input cursor for every packed argument.
  let (inCurBinds, m1, m2) = case inLocA of
        [] -> (mkLets [], M.empty, M.empty)
        _ ->
          let projs = concatMap (\(e, t) -> mkInProjs e t) (zip (map VarE funArgs) in_tys)
              inputLocOrder = concatMap (L2.locsInTy . unTy2) in_tys
              inLocAByInputOrder =
                [ loca
                | inputLoc <- inputLocOrder
                , loca <- inLocA
                , toLocVar loca == inputLoc
                ]
              (bnds, m1f, m2f) =
                foldr
                  ( \(loca, proj) (bn, m11, m22) ->
                      let loc = toLocVar loca
                          reg = toRegVar loca
                          modality = getModality loca
                          var_for_loc = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv'') of
                            Just v -> v
                            Nothing -> error "cursorizeFunDef: unexpected location variable"
                          needs_to_be_mutable = isMutModality' modality
                          --needs_to_be_mutable = case loc of 
                          --                           Single{} -> False
                          --                           SoA{} -> True && useMutableCursors
                          packed_cursor_ty = getCursorizeTyFromLocVar modality needs_to_be_mutable loc
                          m11' = case (isMutModality' modality) of
                                            True -> let varNameToUseForLoc = case proj of 
                                                                                  VarE v -> v
                                                                                  _ -> var_for_loc 
                                                      in updateMutableLocPtsToEnv loc m11 (varNameToUseForLoc, Just loc, Just reg, S.insert var_for_loc S.empty) False
                                            False -> m11
                          m22' = case (isMutModality' modality) of 
                                            True -> let varNameToUseForLoc = case proj of 
                                                                                  VarE v -> v
                                                                                  _ -> var_for_loc 
                                                     in M.insert loc (varNameToUseForLoc, Just loc, Just reg, S.insert var_for_loc S.empty) m22
                                            False -> m22
                       in (bn ++ [(var_for_loc, [], packed_cursor_ty, proj)], m11', m22')
                  ) ([], M.empty, M.empty) (zip inLocAByInputOrder projs)
                  -- [((unwrapLocVar loc),[],CursorTy,proj) | (loc,proj) <- zip inLocs projs]
           in dbgTrace (minChatLvl) "Printing in inCurBinds: " dbgTrace (minChatLvl) (sdoc (bnds)) dbgTrace (minChatLvl) "End printing in inCurBinds.\n" (mkLets bnds, m1f, m2f)

      initTyEnv =
        M.fromList $
          (map (\(a, b) -> (a, MkTy2 (cursorizeInTy useMutableCursors Nothing (unTy2 b)))) $ zip funArgs in_tys)
            ++ ( concatMap
                   ( \(LRM l r m) ->
                       let var_for_loc = case (M.lookup (fromLocVarToFreeVarsTy l) freeVarToVarEnv'') of
                             Just v -> v
                             Nothing -> error "cursorizeFunDef: unexpected location variable"
                           packed_cursor_ty = getCursorizeTyFromLocVar' (Just m) useMutableCursors l
                           loc_entry = (var_for_loc, packed_cursor_ty)
                           var_for_reg = case (M.lookup (fromRegVarToFreeVarsTy (toEndVRegVar $ regionToVar r)) freeVarToVarEnv'') of
                             Just v -> v
                             Nothing -> error "cursorizeFunDef: unexpected region variable"
                           reg_entry = (var_for_reg, packed_cursor_ty)
                        in [loc_entry, reg_entry]
                   )
                   (locVars funTy)
               )

      initTyEnvl =
        M.fromList $
          ( map
              ( \(a, b) -> case (unTy2 b) of
                  PackedTy _ l -> (a, Just l)
                  _ -> (a, Nothing)
              )
              $ zip funArgs in_tys
          )
            ++ ( concatMap
                   ( \(LRM l r _) ->
                       let var_for_loc = case (M.lookup (fromLocVarToFreeVarsTy l) freeVarToVarEnv'') of
                             Just v -> v
                             Nothing -> error "cursorizeFunDef: unexpected location variable"
                           packed_cursor_ty = case l of
                             Single _ -> Just l
                             SoA _ fields -> Just l
                           loc_entry = (var_for_loc, packed_cursor_ty)
                           var_for_reg = case (M.lookup (fromRegVarToFreeVarsTy (toEndVRegVar $ regionToVar r)) freeVarToVarEnv'') of
                             Just v -> v
                             Nothing -> error "cursorizeFunDef: unexpected region variable"
                           reg_entry = (var_for_reg, packed_cursor_ty)
                        in [loc_entry, reg_entry]
                   )
                   (locVars funTy)
               )

      funargs =
        ( L.map
            ( \r -> case (M.lookup (fromRegVarToFreeVarsTy r) freeVarToVarEnv') of
                Just v -> v
                Nothing -> error "cursorizeFunDef: unexpected region variable"
            )
            regBinds
        )
          ++ ( L.map
                 ( \b -> case (M.lookup (fromLocVarToFreeVarsTy b) freeVarToVarEnv') of
                     Just v -> v
                     Nothing -> error "cursorizeFunDef: unexpected location variable"
                 )
                 outCurBinds
             )
          ++ ( L.map
                 ( \v -> case (M.lookup (fromVarToFreeVarsTy v) freeVarToVarEnv') of
                     Just v -> v
                     Nothing -> error "cursorizeFunDef: unexpected variable"
                 )
                 funArgs
             )

  {- Get the regions out before hand, these can be eliminated later on -}

  let noDeadFieldElim = L.isPrefixOf "_traverse_" (fromVar funName)
  let denv0 = if noDeadFieldElim then markNoDeadFieldElim M.empty else M.empty
  bod <-
    if hasPacked (unTy2 out_ty)
      then
        do 
          (funBody', _, _, _) <-  cursorizePackedExp m1 m2 useMutableCursors storeScalarCounts False freeVarToVarEnv'' initTyEnvl ddefs fundefs denv0 initTyEnv M.empty funBody
          return $ fromDi funBody'
      else do 
        (funBody', _, _, _) <- cursorizeExp m1 m2 useMutableCursors storeScalarCounts False freeVarToVarEnv'' initTyEnvl ddefs fundefs denv0 initTyEnv M.empty funBody
        return funBody'

  let bod' = inCurBinds bod
      fn = FunDef funName funargs funTy' bod' funMeta
  dbgTrace (minChatLvl) "Print in cursorizeFunDef: " dbgTrace (minChatLvl) (sdoc (initTyEnv, locVars funTy)) dbgTrace (minChatLvl) "End cursorizeFunDef\n" return fn
  where
    -- \| The only difference between this and L3.cursorizeTy is that here,
    --   packed types are replaced by a single CursorTy instead of
    --   a tuple (CursorTy,CursorTy). This is because only `start` cursors are
    --   passed in for packed function arguments.
    {- Removing the polymorphism, since this function is local to cursorize and all code before cursorize uses LocVar -}
    cursorizeInTy :: Bool -> Maybe L2.Modality -> UrTy LocVar -> UrTy b
    cursorizeInTy useMutableCursors modality ty =
      case ty of
        IntTy -> IntTy
        CharTy -> CharTy
        FloatTy -> FloatTy
        SymTy -> SymTy
        BoolTy -> BoolTy
        ProdTy ls -> ProdTy $ L.map (cursorizeInTy useMutableCursors modality) ls
        SymDictTy ar _ty -> SymDictTy ar CursorTy
        PDictTy k v -> PDictTy (cursorizeInTy useMutableCursors modality k) (cursorizeInTy useMutableCursors modality v)
        PackedTy _ l -> if useMutableCursors 
                        then case l of 
                                Single{} -> MutCursorTy
                                SoA{} -> getCursorizeTyFromLocVar'' modality useMutableCursors l
                        else getCursorizeTyFromLocVar'' modality useMutableCursors l
        VectorTy el_ty -> VectorTy $ cursorizeInTy useMutableCursors modality el_ty
        ListTy el_ty -> ListTy $ cursorizeInTy useMutableCursors modality el_ty
        PtrTy -> PtrTy
        CursorTy -> CursorTy
        MutCursorTy -> MutCursorTy
        CursorArrayTy size -> CursorArrayTy size
        ArenaTy -> ArenaTy
        SymSetTy -> SymSetTy
        SymHashTy -> SymHashTy
        IntHashTy -> IntHashTy

    {-

    Build projections for packed values in the input type
    This is used to create bindings for input location variables.

        >>> mkInProjs e (PackedTy "T" "l")
        [VarE (Var "funArg")]

        >>> mkInProjs e (ProdTy [IntTy,PackedTy "T" "l"])
        [ProjE 1 VarE (Var "funArg")]

        >>> mkInProje e (ProdTy [ProdTy [PackedTy "T" "l", PackedTy "T" "l"], IntTy])
        [ProjE 0 ProjE 0 e, ProjE 1 ProjE 0 e]

        >>> mkInProje e (ProdTy [PackedTy "T" "l",
                                 IntTy,
                                 ProdTy [PackedTy "T" "l",
                                         ProdTy [PackedTy "T" "l", PackedTy "T" "l"]]])
        [ProjE 0 e,ProjE 0 ProjE 2 e,ProjE 0 ProjE 1 ProjE 2 e,ProjE 1 ProjE 1 ProjE 2 e]

    -}
    mkInProjs :: Exp3 -> Ty2 -> [Exp3]
    mkInProjs e0 ty0 = go [] e0 ty0
      where
        go :: [Exp3] -> Exp3 -> Ty2 -> [Exp3]
        go acc e ty =
          case unTy2 ty of
            PackedTy {} -> acc ++ [e]
            ProdTy tys ->
              L.foldl
                (\acc2 (ty', n) -> go acc2 (mkProj n e) ty')
                acc
                (zip (map MkTy2 tys) [0 ..])
            _ -> acc

    cursorizeArrowTy :: Bool -> ArrowTy2 Ty2 -> ([Ty3], Ty3)
    cursorizeArrowTy useMutableCursorsRec ty@ArrowTy2 {arrIns, arrOut, locVars, locRets} =
      let -- Regions corresponding to ouput cursors. (See [Threading regions])
          numOutRegs = length $ (outRegVars ty) ++ (L2.outRegVarsMutable ty)
          -- outRegs = L.map (\_ -> CursorTy) [1..numOutRegs]

          outRegs =
            (
              L.map
              ( \r -> getCursorizeTyFromRegVar'' (Just Output) useMutableCursorsRec r
              )
              (outRegVars ty)
            )
            ++

            (
              L.map
              ( \r -> getCursorizeTyFromRegVar'' (Just OutputMutable) useMutableCursorsRec r
              )
              (L2.outRegVarsMutable ty)
            )


          -- Adding additional outputs corresponding to end-of-input-value witnesses
          -- We've already computed additional location return value in RouteEnds
          -- ret_curs = L.map (\_ -> CursorTy) locRets

          ret_curs =
            L.map
              ( \lret -> case lret of
                  EndOf (LRM l _ m) -> getCursorizeTyFromLocVar'' (Just m) useMutableCursorsRec l
              )
              locRets

          out_curs = inRegs ++ outRegs ++ ret_curs
          
          -- The output type contains start and end cursors for output regions. 
          -- In case of a tail recursive optimization, we should try to fully 
          -- get rid of the return value in case its a packed type. 
          -- It the return value is not a packed type then we should keep it.
          out_ty = case out_curs of
            [] -> unTy2 arrOut
            _ -> case useMutableCursorsRec of 
                        True -> unTy2 arrOut 
                        False -> ProdTy $ out_curs ++ [unTy2 arrOut]

          -- Packed types in the output then become end-cursors for those same destinations.
          -- For now, in case we deem that a function is tail recursive, this includes cases 
          -- where we have tailModuluCons. We can try to get rid of the return value fully, 
          -- in case its a packed type?? 
          -- If not a packed type we should keep this return value in the function signature.
          -- TODO: Vidush is this truly the case?
          newOut =
            mapPacked
              (\var loc -> case useMutableCursorsRec of 
                                  False -> ProdTy [getCursorizeTyFromLocVar'' Nothing useMutableCursorsRec loc, getCursorizeTyFromLocVar'' Nothing useMutableCursorsRec loc]
                                  -- In case of a packed type where we are trying to tail call optimize the function we 
                                  -- would like to return void if we can.
                                  True -> ProdTy []
              )
              out_ty

          newOut' = dbgTrace (minChatLvl) "Print in cursorize arrowTy: " dbgTrace (minChatLvl) (sdoc (funName, outRegs, ret_curs, out_curs, out_ty, newOut, arrIns)) dbgTrace (minChatLvl) "End printing in arrowTy.\n" case newOut of
            SymDictTy a _ -> SymDictTy a CursorTy
            _ -> newOut

          -- Adding additional input arguments for the destination cursors to which outputs
          -- are written.
          outCurs = filter (\(LRM _ _ m) -> m == Output || m == OutputMutable) locVars
          outCurTys =
            map
              ( \(LRM l _ m) -> getCursorizeTyFromLocVar'' (Just m) useMutableCursorsRec l
              )
              outCurs
          inRegs =
            map
              ( \(LRM _ r m) -> getCursorizeTyFromRegVar'' (Just m) useMutableCursorsRec (regionToVar r)
              )
              (L2.inRegVars' ty)
          in_tys = inRegs ++ outRegs ++ outCurTys ++ (map unTy2 arrIns)

          -- Packed types in the input now become (read-only) cursors.

          newIns = map (cursorizeInTy useMutableCursorsRec Nothing) in_tys
            --if useSoA
              --then map (cursorizeInTy) in_tys
              --else map (constPacked CursorTy) in_tys
       in dbgTrace (minChatLvl) "Print in_tys" dbgTrace (minChatLvl) (sdoc (out_ty, in_tys)) dbgTrace (minChatLvl) "End in_tys\n" (map stripTyLocs newIns, stripTyLocs newOut')

-- | Cursorize expressions NOT producing `Packed` values
cursorizeExp ::
  MutableLocPtsToEnv -> 
  MutableLocOldValueEnv ->
  Bool -> 
  Bool ->
  Bool ->
  M.Map FreeVarsTy Var ->
  TyEnv Var (Maybe LocVar) ->
  DDefs Ty2 ->
  FunDefs2 ->
  DepEnv ->
  TyEnv Var Ty2 ->
  SyncEnv ->
  Exp2 ->
  PassM (Exp3, M.Map FreeVarsTy Var, MutableLocPtsToEnv, MutableLocOldValueEnv)
cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv ex =
  case ex of
    VarE v -> return $ (VarE v, freeVarToVarEnv, m1, m2)
    LitE n -> return $ (LitE n, freeVarToVarEnv, m1, m2)
    CharE c -> return $ (CharE c, freeVarToVarEnv, m1, m2)
    FloatE n -> return $ (FloatE n, freeVarToVarEnv, m1, m2)
    LitSymE n -> return $ (LitSymE n, freeVarToVarEnv, m1, m2)
    AppE {} -> cursorizeAppE m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv ex
    PrimAppE RequestSizeOf [arg] -> do
      let (VarE v) = arg
      case M.lookup v tenv of
        Nothing -> error $ "cursorizeExp: Unbound variable: " ++ sdoc v
        Just ty ->
          if isPackedTy (unTy2 ty)
            then pure $ (Ext $ SubPtr (toEndV v) v, freeVarToVarEnv, m1, m2)
            else do
              dflags <- getDynFlags
              pure $ (LitE $ fromJust $ sizeOfTyD dflags (unTy2 ty), freeVarToVarEnv, m1, m2)
    PrimAppE pr args -> do 
                         res <- mapM (go insideTimeIt m1 m2 freeVarToVarEnv) args
                         let args' = map fst4 res
                         let freeEnvs = map snd4 res 
                         let freeVarToVarEnv' = M.unions freeEnvs
                         let m1s = map thd4 res
                         let m1' = M.unions m1s
                         let m2s = map fth4 res
                         let m2' = M.unions m2s
                         ret_expr <- return $ PrimAppE (toL3Prim pr) args'
                         return (ret_expr, freeVarToVarEnv', m1', m2')
    LetE (v, _locs, _ty, (PrimAppE (ReadPackedFile path tyc reg ty2) [])) bod -> do
      freeVarToVarEnv' <-
        foldrM
          ( \loc env -> case loc of
              EndOfReg r _ er -> do
                env' <- insertRegInVarEnv r env
                env'' <- insertRegInVarEnv er env'
                return env''
              EndWitness lrem loc -> do
                env' <- insertLocInVarEnv loc env
                env'' <- insertLocInVarEnv (lremLoc lrem) env'
                env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                return env''''
              Loc lrem -> do
                env' <- insertLocInVarEnv (lremLoc lrem) env
                env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                env''' <- insertRegInVarEnv (lremReg lrem) env''
                return env'''
              Reg r _ -> do
                env' <- insertRegInVarEnv r env
                return env'
              EndOfReg_Tagged r -> do
                env' <- insertRegInVarEnv r env
                return env'
          )
          freeVarToVarEnv
          _locs
      (ret_e, freeVarToVarEnv'', m1', m2') <- cursorizeReadPackedFile m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv tenv senv True v path tyc reg ty2 bod
      return (ret_e, M.union freeVarToVarEnv' freeVarToVarEnv'', m1', m2')
    LetE (_v, _locs, _ty, (MkProdE _ls)) _bod -> do
      freeVarToVarEnv' <-
        foldrM
          ( \loc env -> case loc of
              EndOfReg r _ er -> do
                env' <- insertRegInVarEnv r env
                env'' <- insertRegInVarEnv er env'
                return env''
              EndWitness lrem loc -> do
                env' <- insertLocInVarEnv loc env
                env'' <- insertLocInVarEnv (lremLoc lrem) env'
                env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                return env''''
              Loc lrem -> do
                env' <- insertLocInVarEnv (lremLoc lrem) env
                env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                env''' <- insertRegInVarEnv (lremReg lrem) env''
                return env'''
              Reg r _ -> do
                env' <- insertRegInVarEnv r env
                return env'
              EndOfReg_Tagged r -> do
                env' <- insertRegInVarEnv r env
                return env'
          )
          freeVarToVarEnv
          _locs
      (ret_prod, freeVarToVarEnv'', m1', m2') <- cursorizeProd m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv False ddfs fundefs denv tenv senv ex
      return $ (ret_prod, M.union freeVarToVarEnv' freeVarToVarEnv'', m1', m2')
    LetE (_v, _locs, ty, ProjE {}) _bod | isPackedTy (unTy2 ty) -> do
      freeVarToVarEnv' <-
        foldrM
          ( \loc env -> case loc of
              EndOfReg r _ er -> do
                env' <- insertRegInVarEnv r env
                env'' <- insertRegInVarEnv er env'
                return env''
              EndWitness lrem loc -> do
                env' <- insertLocInVarEnv loc env
                env'' <- insertLocInVarEnv (lremLoc lrem) env'
                env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                return env''''
              Loc lrem -> do
                env' <- insertLocInVarEnv (lremLoc lrem) env
                env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                env''' <- insertRegInVarEnv (lremReg lrem) env''
                return env'''
              Reg r _ -> do
                env' <- insertRegInVarEnv r env
                return env'
              EndOfReg_Tagged r -> do
                env' <- insertRegInVarEnv r env
                return env'
          )
          freeVarToVarEnv
          _locs
      (ret_e, freeVarToVarEnv'', m1', m2') <- cursorizeProj m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv False ddfs fundefs denv tenv senv ex
      return $ (ret_e, M.union freeVarToVarEnv' freeVarToVarEnv'', m1', m2')
    LetE (_v, _locs, _ty, SpawnE {}) _bod -> do
      freeVarToVarEnv' <-
        foldrM
          ( \loc env -> case loc of
              EndOfReg r _ er -> do
                env' <- insertRegInVarEnv r env
                env'' <- insertRegInVarEnv er env'
                return env''
              EndWitness lrem loc -> do
                env' <- insertLocInVarEnv loc env
                env'' <- insertLocInVarEnv (lremLoc lrem) env'
                env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                return env''''
              Loc lrem -> do
                env' <- insertLocInVarEnv (lremLoc lrem) env
                env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                env''' <- insertRegInVarEnv (lremReg lrem) env''
                return env'''
              Reg r _ -> do
                env' <- insertRegInVarEnv r env
                return env'
              EndOfReg_Tagged r -> do
                env' <- insertRegInVarEnv r env
                return env'
          )
          freeVarToVarEnv
          _locs
      (ret_e, freeVarToVarEnv'', m1', m2') <- cursorizeSpawn m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv False ddfs fundefs denv tenv senv ex
      return (ret_e, M.union freeVarToVarEnv' freeVarToVarEnv'', m1', m2')
    LetE (_v, _locs, _ty, SyncE) _bod -> do
      freeVarToVarEnv' <-
        foldrM
          ( \loc env -> case loc of
              EndOfReg r _ er -> do
                env' <- insertRegInVarEnv r env
                env'' <- insertRegInVarEnv er env'
                return env''
              EndWitness lrem loc -> do
                env' <- insertLocInVarEnv loc env
                env'' <- insertLocInVarEnv (lremLoc lrem) env'
                env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                return env''''
              Loc lrem -> do
                env' <- insertLocInVarEnv (lremLoc lrem) env
                env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                env''' <- insertRegInVarEnv (lremReg lrem) env''
                return env'''
              Reg r _ -> do
                env' <- insertRegInVarEnv r env
                return env'
              EndOfReg_Tagged r -> do
                env' <- insertRegInVarEnv r env
                return env'
          )
          freeVarToVarEnv
          _locs
      (ret_e, freeVarToVarEnv'', m1', m2') <- cursorizeSync m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv False ddfs fundefs denv tenv senv ex
      return $ (ret_e, M.union freeVarToVarEnv' freeVarToVarEnv'', m1', m2')
    LetE (v, _locs, ty, rhs@(Ext (SSPush _ start _ _))) bod -> do
      case M.lookup (unwrapLocVar start) tenv of
        Nothing -> go insideTimeIt m1 m2 freeVarToVarEnv bod
        Just {} -> do
          (rhs', fenv1, m1', m2') <- go insideTimeIt m1 m2 freeVarToVarEnv rhs
          (bod', fenv2, m1'', m2'') <- go insideTimeIt m1' m2' fenv1 bod
          let ty' = cursorizeTy fenv2 m1'' m2'' useMutableCursorsCall Nothing (unTy2 ty)
          return $ (LetE (v, [], ty', rhs') bod', fenv2, m1'', m2'')
    LetE (v, _locs, ty, rhs@(Ext (SSPop _ start _))) bod ->
      case M.lookup (unwrapLocVar start) tenv of
        Nothing -> go insideTimeIt m1 m2 freeVarToVarEnv bod
        Just {} -> do
          (rhs', fenv1, m1', m2') <- go insideTimeIt m1 m2 freeVarToVarEnv rhs
          (bod', fenv2, m1'', m2'') <- go insideTimeIt m1' m2' fenv1 bod
          let ty' = cursorizeTy fenv2 m1'' m2'' useMutableCursorsCall Nothing (unTy2 ty)
          return $ (LetE (v, [], ty', rhs') bod', fenv2, m1'', m2'')

    -- LetE bnd@(v, _locs, ty, rhs) bod -> case rhs of
    --   Ext (BoundsCheck i bound cur) -> do
    --     let bound_loc = toLocVar bound
    --     let bound_var = case (M.lookup (fromLocVarToFreeVarsTy bound_loc) freeVarToVarEnv) of
    --                                       Just v -> v
    --                                       Nothing -> error $ "cursorizeExp: BoundsCheck: unexpected location variable" ++ sdoc bound_loc
    --     let cur_loc = toLocVar cur
    --     let cur_var = case (M.lookup (fromLocVarToFreeVarsTy cur_loc) freeVarToVarEnv) of
    --                                      Just v -> v
    --                                      Nothing -> error $ "cursorizeExp: BoundsCheck: unexpected location variable" ++ sdoc cur_loc
    --     exp' <- return $Ext $ L3.BoundsCheck i bound_var cur_var
    --     --exp' <- if isBound cur_var tenv
    --     --       then return $ Ext $ L3.BoundsCheck i bound_var cur_var
    --     --       else do
    --     --            let denv' = M.insertWith (++) (cur_loc) [((unwrapLocVar lvar),[],CursorTy,rhs)] denv
    --     --         return $ Ext $ L3.BoundsCheck i bound_var cur_var --Left$ M.insertWith (++) ((toLocVar) loc) [((unwrapLocVar lvar),[],CursorTy,rhs)] denv
    --     return exp'
    --   _ -> cursorizeLet freeVarToVarEnv False ddfs fundefs denv tenv senv bnd bod

    LetE bnd@(_, _locs, _, _) bod -> do
      freeVarToVarEnv' <-
        foldrM
          ( \loc env -> case loc of
              EndOfReg r _ er -> do
                env' <- insertRegInVarEnv r env
                env'' <- insertRegInVarEnv er env'
                return env''
              EndWitness lrem loc -> do
                env' <- insertLocInVarEnv loc env
                env'' <- insertLocInVarEnv (lremLoc lrem) env'
                env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                return env''''
              Loc lrem -> do
                env' <- insertLocInVarEnv (lremLoc lrem) env
                env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                env''' <- insertRegInVarEnv (lremReg lrem) env''
                return env'''
              Reg r _ -> do
                env' <- insertRegInVarEnv r env
                return env'
              EndOfReg_Tagged r -> do
                env' <- insertRegInVarEnv r env
                return env'
          )
          freeVarToVarEnv
          _locs
      (ret_e, freeVarToVarEnv'', m1', m2') <- cursorizeLet m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv False ddfs fundefs denv tenv senv bnd bod
      return $ (ret_e, M.unions [freeVarToVarEnv, freeVarToVarEnv', freeVarToVarEnv''], m1', m2')
    IfE a b c -> do 
                  (a', e1, m1', m2') <- go insideTimeIt m1 m2 freeVarToVarEnv a
                  (b', e2, m1'', m2'') <- go insideTimeIt m1' m2' freeVarToVarEnv b
                  (c', e3, m1''', m2''') <- go insideTimeIt m1'' m2'' freeVarToVarEnv c
                  return (IfE a' b' c', M.unions [freeVarToVarEnv, e1, e2, e3], m1''', m2''')
    MkProdE ls -> do
      case ls of 
          [] -> do
                return $ (MkProdE [], freeVarToVarEnv, m1, m2)
          _ -> do
                res <- mapM (go insideTimeIt m1 m2 freeVarToVarEnv) ls
                let ls' = map fst4 res
                let envs = map snd4 res
                let m1s = map thd4 res 
                let m2s = map fth4 res      
                return $ (MkProdE ls', M.unions envs, M.unions m1s, M.unions m2s)
    ProjE i e -> do 
                  (e', env, m1', m2') <- go insideTimeIt m1 m2 freeVarToVarEnv e
                  return (ProjE i e', env, m1', m2')
    -- Eg. leftmost
    CaseE scrt brs -> do
      -- ASSUMPTION: scrt is flat
      freeVarToVarEnv' <-
        foldrM
          ( \(dcon, vlocs, rhs) acc -> do
              case vlocs of
                [] -> return acc
                _ -> do
                  acc' <-
                    foldrM
                      ( \(v, l) acc'' -> do
                          case (toLocVar l) of
                            Single l' -> return $ M.insert (fromLocVarToFreeVarsTy (toLocVar l)) l' acc''
                            SoA _ _ -> do
                              if M.member (fromLocVarToFreeVarsTy (toLocVar l)) acc''
                                then return acc''
                                else do
                                  name <- gensym "cursor_ptr"
                                  return $ M.insert (fromLocVarToFreeVarsTy (toLocVar l)) name acc''
                      )
                      acc
                      vlocs
                  return acc'
          )
          freeVarToVarEnv
          brs
      let (VarE v) = scrt
      let ty_of_scrut = case (M.lookup v tenv) of
            Just (MkTy2 ty) -> ty
            Nothing -> error "unpackDataCon: unexpected location variable"
      dcon_var <- gensym "dcon"
      -- Vidush: 
      -- We need to check if the scrutinee variable is a mutable variable.
      let scrutMutable = checkIfVarIsMutable v m1
      {-VS: TODO: get location of scrutinee, send it to unpack data con. Get the L2 location!!!-}
      -- (dcon_var, dcon_let_bind) <- case scrutMutable of 
      --                                               True -> do 
      --                                                       dcon_var <- gensym "dcon"
      --                                                       dcon_deref <- gensym "deref_dcon"
      --                                                       let dcon_let = [(dcon_var, [], MutCursorTy, Ext $ AddrOfCursor $ Ext $ IndexCursorArray v 0)]
      --                                                       let deref_dcon = [(dcon_deref, [], CursorTy, Ext $ DerefMutCursor dcon_var)]
      --                                                       let dcon_let_bind = mkLets $ dcon_let ++ deref_dcon
      --                                                       return (dcon_deref, dcon_let_bind)
      --                                               False -> do 
      --                                                        dcon_var <- gensym "dcon"
      --                                                        let dcon_let = [(dcon_var, [], CursorTy, Ext $ IndexCursorArray v 0)]
      --                                                        let dcon_let_bind = mkLets dcon_let
      --                                                        return (dcon_var, dcon_let_bind)
      let all_buffers_alive =
            S.fromList
              [ (dcon, idx)
              | (dcon, var_locs, _) <- brs,
                idx <- [0 .. length var_locs - 1]
              ]
      let vars_mentioned = varsMentionedInExp ex
      let alive_buffers =
            if isNoDeadFieldElim denv
              then all_buffers_alive
              else
                foldr
                  ( \(dcon, var_locs, _) acc ->
                      foldr
                        (\(idx, (var, _)) acc' -> if S.member var vars_mentioned then S.insert (dcon, idx) acc' else acc')
                        acc
                        (zip [0 ..] var_locs)
                  )
                  S.empty
                  brs
      --let alive_buffers = S.empty
      case ty_of_scrut of
        CursorTy -> do 
          case_expr <- 
            CaseE (VarE $ v)
            <$> mapM (unpackDataCon alive_buffers m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv senv False v) brs
          -- Vidush: For now we just return the environment.
          dbgTrace (minChatLvl) "Print in CursorTy: " dbgTrace (minChatLvl) (sdoc (ty_of_scrut, scrt, alive_buffers)) dbgTrace (minChatLvl) "End printing CursorTy.\n" return (case_expr, freeVarToVarEnv, m1, m2)
        -- We need to dereference a mutable cursor to get its value.
        MutCursorTy -> do
                       deref_val <- gensym "deref_val"
                       let additional_deref_let = mkLets [(deref_val, [], CursorTy, Ext $ DerefMutCursor v)]
                       let tenv' = M.insert deref_val (MkTy2 CursorTy) tenv
                       let output_mut_loc_scrut = findMutableLocationPointingToVar v m1
                       (m1', m2') <- case output_mut_loc_scrut of 
                                            Nothing -> error "Did not expect mutable cursor!\n"
                                            Just outloc -> do let m1i = updateMutableLocPtsToEnv outloc m1 (deref_val, Just outloc, Nothing, S.empty) False
                                                              let m2i = M.insert outloc (deref_val, Just outloc, Nothing, S.empty) m2
                                                              return (m1i, m2i)
                       case_expr <- additional_deref_let 
                                    <$> CaseE (VarE $ deref_val)
                                    <$> mapM (unpackDataCon alive_buffers m1' m2' useMutableCursorsCall emitScalarCountBumps insideTimeIt dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv' senv True deref_val) brs
                       dbgTrace (minChatLvl) "Print in MutCursorCase: " dbgTrace (minChatLvl) (sdoc (ty_of_scrut, scrt, alive_buffers)) dbgTrace (minChatLvl) "End printing MutCursorCase.\n" return (case_expr, freeVarToVarEnv, m1', m2')
        CursorArrayTy {} -> do
          -- check if v points to any mutable location
          let mut_loc_pointing_to_v = findMutableLocationPointingToVar v m1
          (dcon_var', dcon_let, m1', m2', freeVarToVarEnv'') <- case mut_loc_pointing_to_v of 
                                                            Nothing -> do 
                                                                       let dcon_let_bind = [(dcon_var, [], CursorTy, Ext $ IndexCursorArray v 0)]
                                                                       dbgTrace (minChatLvl) "Print in case Cursor ArrayTy: " dbgTrace (minChatLvl) (sdoc (mut_loc_pointing_to_v, v, alive_buffers)) dbgTrace (minChatLvl) "End in print case Nothing cursor array ty.\n" return (dcon_var, dcon_let_bind, m1, m2, freeVarToVarEnv')
                                                            Just ml -> do
                                                                        dcon_var_deref <- gensym "deref_dcon_var"
                                                                        let dcon_loc = getDconLoc ml
                                                                        let (dcon_loc_name, freeVarToVarEnv_i) = if M.member (fromLocVarToFreeVarsTy dcon_loc) freeVarToVarEnv' 
                                                                                                                 then (getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy dcon_loc), freeVarToVarEnv')
                                                                                                                 else case dcon_loc of 
                                                                                                                        Single l -> (l, M.insert (fromLocVarToFreeVarsTy dcon_loc) l freeVarToVarEnv')   
                                                                                                                        SoA{} -> error "Did not expect SoA location for data constructor region!\n"
                                                                        let dcon_let_bind = [(dcon_loc_name, [], MutCursorTy, Ext $ AddrOfCursor $ Ext $ IndexCursorArray v 0)]
                                                                        let m1i = updateMutableLocPtsToEnv dcon_loc m1 (dcon_var_deref, Just dcon_loc, Nothing, S.empty) True
                                                                        let m2i = M.insert dcon_loc (dcon_var_deref, Just dcon_loc, Nothing, S.empty) m2
                                                                        let deref_dcon_mut = [(dcon_var_deref, [], CursorTy, Ext $ DerefMutCursor dcon_loc_name)]
                                                                        dbgTrace (minChatLvl) "Print in case Cursor ArrayTy: " dbgTrace (minChatLvl) (sdoc (mut_loc_pointing_to_v, v, alive_buffers)) dbgTrace (minChatLvl) "End in print case Just ml cursor array ty.\n" return (dcon_var_deref, (dcon_let_bind ++ deref_dcon_mut), m1i, m2i, freeVarToVarEnv_i)
          --let dcon_let = [(dcon_var, [], CursorTy, Ext $ IndexCursorArray v 0)]
          let dcon_let_bind = mkLets dcon_let
          case_expr <- dcon_let_bind
            <$> CaseE (VarE $ dcon_var')
            <$> mapM (unpackDataCon alive_buffers m1' m2' useMutableCursorsCall emitScalarCountBumps insideTimeIt dcon_var' freeVarToVarEnv'' lenv ddfs fundefs denv tenv senv False v) brs
          dbgTrace (minChatLvl) "Print in CursorArrayTy: " dbgTrace (minChatLvl) (sdoc (ty_of_scrut, scrt)) dbgTrace (minChatLvl) "End printing CursorArrayTy.\n" return (case_expr, freeVarToVarEnv'', m1', m2')
        PackedTy _ scrutLoc -> case scrutLoc of
          Single _ -> do
            case_expr <- CaseE (VarE $ v)
                <$> mapM (unpackDataCon alive_buffers m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv senv False v) brs
            dbgTrace (minChatLvl) "Print in PackedTy: " dbgTrace (minChatLvl) (sdoc (ty_of_scrut, scrt)) dbgTrace (minChatLvl) "End printing PackedTy Single.\n" return (case_expr, freeVarToVarEnv', m1, m2)

          SoA _ _ -> do
            -- check if v points to any mutable location
            let mut_loc_pointing_to_v = findMutableLocationPointingToVar v m1
            (dcon_var', dcon_let, m1', m2', freeVarToVarEnv'') <- case mut_loc_pointing_to_v of 
                                                            Nothing -> do 
                                                                       let dcon_let_bind = [(dcon_var, [], CursorTy, Ext $ IndexCursorArray v 0)]
                                                                       dbgTrace (minChatLvl) "Print in case Cursor ArrayTy: " dbgTrace (minChatLvl) (sdoc (mut_loc_pointing_to_v, v)) dbgTrace (minChatLvl) "End in print case Nothing cursor array ty.\n" return (dcon_var, dcon_let_bind, m1, m2, freeVarToVarEnv')
                                                            Just ml -> do
                                                                        dcon_var_deref <- gensym "deref_dcon_var"
                                                                        let dcon_loc = getDconLoc ml
                                                                        let (dcon_loc_name, freeVarToVarEnv_i) = if M.member (fromLocVarToFreeVarsTy dcon_loc) freeVarToVarEnv' 
                                                                                                                 then (getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy dcon_loc), freeVarToVarEnv')
                                                                                                                 else case dcon_loc of 
                                                                                                                        Single l -> (l, M.insert (fromLocVarToFreeVarsTy dcon_loc) l freeVarToVarEnv')   
                                                                                                                        SoA{} -> error "Did not expect SoA location for data constructor region!\n"
                                                                        let dcon_let_bind = [(dcon_loc_name, [], MutCursorTy, Ext $ AddrOfCursor $ Ext $ IndexCursorArray v 0)]
                                                                        let m1i = updateMutableLocPtsToEnv dcon_loc m1 (dcon_var_deref, Just dcon_loc, Nothing, S.empty) True
                                                                        let m2i = M.insert dcon_loc (dcon_var_deref, Just dcon_loc, Nothing, S.empty) m2
                                                                        let deref_dcon_mut = [(dcon_var_deref, [], CursorTy, Ext $ DerefMutCursor dcon_loc_name)]
                                                                        dbgTrace (minChatLvl) "Print in case Cursor ArrayTy: " dbgTrace (minChatLvl) (sdoc (mut_loc_pointing_to_v, v)) dbgTrace (minChatLvl) "End in print case Just ml cursor array ty.\n" return (dcon_var_deref, (dcon_let_bind ++ deref_dcon_mut), m1i, m2i, freeVarToVarEnv_i)
            let dcon_let_bind = mkLets dcon_let
            case_expr <- dcon_let_bind
              <$> CaseE (VarE $ dcon_var')
              <$> mapM (unpackDataCon alive_buffers m1' m2' useMutableCursorsCall emitScalarCountBumps insideTimeIt dcon_var' freeVarToVarEnv'' lenv ddfs fundefs denv tenv senv False v) brs
            dbgTrace (minChatLvl) "Print in PackedTy: " dbgTrace (minChatLvl) (sdoc (ty_of_scrut, scrt)) dbgTrace (minChatLvl) "End printing PackedTy SoA.\n" return (case_expr, freeVarToVarEnv'', m1', m2')
        
        _ -> do
          case_expr <- CaseE (VarE $ v)
            <$> mapM (unpackDataCon alive_buffers m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv senv False v) brs
          return (case_expr, freeVarToVarEnv', m1, m2)
    
    DataConE _ _ _ -> error $ "cursorizeExp: Should not have encountered DataConE if type is not packed: " ++ ndoc ex
    TimeIt e ty b -> do 
                       (e', env, m1', m2') <- go True m1 m2 freeVarToVarEnv e
                       return (TimeIt e' (stripTyLocs (unTy2 ty)) b, env, m1', m2')

    WithArenaE v e -> do
      (e', env, m1', m2') <- cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv (M.insert v (MkTy2 ArenaTy) tenv) senv e
      return $ (WithArenaE v e', env, m1', m2')
    SpawnE {} -> error "cursorizeExp: Unbound SpawnE"
    SyncE {} -> error "cursorizeExp: Unbound SyncE"
    -- Eg. leftmost
    Ext ext ->
      case ext of
        AddFixed v i -> return $ (Ext $ L3.AddCursor v (L3.LitE i), freeVarToVarEnv, m1, m2)
        RetE locs v -> 
          if useMutableCursorsCall
          then
            return (VarE v, freeVarToVarEnv, m1, m2)
          else
            case locs of
              [] -> return (VarE v, freeVarToVarEnv, m1, m2)
              _ ->
                return
                  (L3.MkProdE $
                    ( map
                        ( \loc ->
                            let loc_to_free_var = fromLocArgToFreeVarsTy loc
                                locs_variable = case (M.lookup (loc_to_free_var) freeVarToVarEnv) of
                                  Just v -> v
                                  Nothing -> case (toLocVar loc) of
                                    Single lvarr -> lvarr
                                    SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
                              in VarE locs_variable
                        ) locs
                    ) ++ [VarE v] , freeVarToVarEnv, m1, m2)
        StartOfPkdCursor cur -> return (VarE cur, freeVarToVarEnv, m1, m2)
        TagCursor a b -> do
          let a_var = case (M.lookup (fromLocVarToFreeVarsTy (toLocVar a)) freeVarToVarEnv) of
                Just v -> v
                Nothing -> case (toLocVar a) of
                  Single l -> l
                  SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
          (b_var, adnl_bnds) <- do
                   let loc_b = toLocVar b
                   if M.member loc_b m1 
                   then
                     do 
                     let (varname, _, _, _):xs = fromJust $ M.lookup loc_b m1
                     case M.lookup varname tenv of 
                                    Nothing -> return (varname, [])
                                    Just ty -> case (unTy2 ty) of
                                                        CursorTy -> return (varname, [])
                                                        MutCursorTy -> do
                                                                       deref_region <- gensym "deref"
                                                                       let bnd = [(deref_region, [], CursorTy, Ext $ DerefMutCursor varname)]
                                                                       return (deref_region, bnd)
                                                        _ -> return (varname, [])
                   else 
                    case (M.lookup (fromRegVarToFreeVarsTy ((fromLocVarToRegVar . toLocVar) b)) freeVarToVarEnv) of
                        Just v -> return (v, [])
                        Nothing -> case (toLocVar b) of
                                      Single l -> return (l, [])
                                      SoA _ _ -> error $ "cursorizeExp: LetLocE: unexpected location variable " ++ show ((fromLocVarToRegVar . toLocVar) b)

          tag_cur_var <- gensym "tag_cur"
          --casted_var <- gensym "cast"
          let ty3_of_field = getCursorizeTyFromLocVar'' (getModality a) False (toLocVar a)
          let ty3_of_field2 = getCursorizeTyFromLocVar (getModality a) False (toLocVar a)
          let tag_inst = case (toLocVar a) of 
                                 Single _ -> adnl_bnds ++ [(tag_cur_var, [], ty3_of_field, Ext $ L3.TagCursor a_var b_var)]
                                 -- in case its an SoA cursor, we mempcpy it. 
                                 SoA{} ->  [ (tag_cur_var, [], ty3_of_field, Ext $ InitCursor ty3_of_field),
                                            ("_", [], ProdTy [], Ext $ MemCpy tag_cur_var a_var ty3_of_field)]
          -- should not need to case anymore                                  
          --let cast_inst = (casted_var, [], CursorTy, Ext $ CastPtr tag_cur_var CursorTy)
          let let_bnd = mkLets $ tag_inst -- ++ [cast_inst]
          return (let_bnd (VarE tag_cur_var), freeVarToVarEnv, m1, m2)

        -- All locations are transformed into cursors here. Location arithmetic
        -- is expressed in terms of corresponding cursor operations.
        -- See `cursorizeLocExp`
        LetLocE locarg rhs bod -> do
          let loc = (toLocVar locarg)
          let ty2_of_loc = if M.member loc m1 
                           then case loc of 
                                     Single{} -> CursorTy
                                     SoA{} -> getCursorizeTyFromLocVar'' (getModality locarg) useMutableCursorsCall loc
                           else getCursorizeTyFromLocVar'' (getModality locarg) useMutableCursorsCall loc
          let ty3_of_loc = if M.member loc m1
                           then case loc of 
                                      Single{} -> CursorTy 
                                      SoA{} -> getCursorizeTyFromLocVar (getModality locarg) useMutableCursorsCall loc
                           else getCursorizeTyFromLocVar (getModality locarg) useMutableCursorsCall loc
          freeVarToVarEnv' <- do
            case loc of
              Single l ->
                if M.member (fromLocVarToFreeVarsTy loc) freeVarToVarEnv
                  then return freeVarToVarEnv
                  else return $ M.insert (fromLocVarToFreeVarsTy loc) l freeVarToVarEnv
              SoA _ _ ->
                if M.member (fromLocVarToFreeVarsTy loc) freeVarToVarEnv
                  then return $ freeVarToVarEnv
                  else do
                    name <- gensym "cursor_ptr"
                    return $ M.insert (fromLocVarToFreeVarsTy loc) name freeVarToVarEnv
          let locs_variable = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv') of
                Just v -> v
                Nothing -> case loc of
                  Single lvarrr -> lvarrr
                  SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
          (rhs_either, m1', m2') <- cursorizeLocExp m1 m2 useMutableCursorsCall freeVarToVarEnv' denv tenv senv locarg rhs
          let (bnds, tenv', m1mextended) = dbgTrace (minChatLvl) "Print envs after cursorizeLocExp: " dbgTrace (minChatLvl) (sdoc (m1', m2')) dbgTrace (minChatLvl) "End print envs after cursorizeLocExp.\n" case M.lookup (fromLocVarToFreeVarsTy loc) denv of
                Nothing -> ([], tenv, m1')
                Just vs ->
                  let vs' = map (\(v, anns, ty, e) ->
                                let e' = case (ty, e) of
                                      (CursorTy, VarE src) -> cursorValueFromMaybeTrackedMut m1' tenv src
                                      _ -> e
                                 in (v, anns, ty, e')) vs
                      extended = M.fromList [(v, MkTy2 CursorTy) | (v, _, CursorTy, _) <- vs']
                      mextended = foldr (\((v, _, _, _)) mfld -> let mutloc = findMutableLocationPointingToVar locs_variable m1'
                                                                          in case mutloc of 
                                                                              Nothing -> mfld
                                                                              Just ml -> updateMutableLocPtsToEnv ml mfld (v, Just ml, Nothing, S.empty) True        
                                        ) m1' vs' 
                   in (vs', M.union extended tenv, mextended)
          case rhs_either of
            -- Check if the location is already bound before. If so, don't
            -- create a duplicate binding. This only happens when we
            -- have indirection _and_ a end-witness for a particular value.
            -- For example, consider a pattern like
            --     (Node^ [(ind_y2, loc_ind_y2), (x1, loc_x1), (y2, loc_y2)] BODY)
            --
            -- occuring in a function like sum-tree.
            --
            -- While unpacking this constructor, we bind y2 to ind_y2.
            -- But since sum-tree traverses it's input, we will enconter
            -- (y2 = end_x1) sometime later in the AST (due to RouteEnds).
            -- We just ignore the second binding for now.
            --
            Right (rhs', bnds', bnds_after, tenv'', senv') -> do
              let tenv''' = M.union tenv' tenv''
              let locs_var = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv') of
                    Just v -> v
                    Nothing -> case loc of
                      Single lvarrr -> lvarrr
                      SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
              case rhs of
                FromEndLE {} ->
                  if isBound locs_var tenv
                    then cursorizeExp m1mextended m2' useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv (M.insert locs_var (MkTy2 ty2_of_loc) tenv''') senv' bod
                    -- Discharge bindings that were waiting on 'loc'.
                    else
                      do 
                        (loc_bnds, m2_for_body) <- case ty3_of_loc of
                          MutCursorTy -> bindMutableLetLoc loc locarg locs_var rhs' m2'
                          _ -> pure ([(locs_var, [], ty3_of_loc, rhs')], m2')
                        (bod', env, m1'', m2'') <- cursorizeExp m1mextended m2_for_body useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv (M.insert locs_var (MkTy2 ty2_of_loc) tenv''') senv' bod
                        return (mkLets (bnds' ++ loc_bnds ++ bnds_after ++ bnds) bod', env, m1'', m2'')
                -- Discharge bindings that were waiting on 'loc'.
                _ -> do 
                     (loc_bnds, m2_for_body) <- case ty3_of_loc of
                       MutCursorTy -> bindMutableLetLoc loc locarg locs_var rhs' m2'
                       _ -> pure ([(locs_var, [], ty3_of_loc, rhs')], m2')
                     (bod', env, m1'', m2'') <- cursorizeExp m1mextended m2_for_body useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv (M.insert locs_var (MkTy2 ty2_of_loc) tenv''') senv bod
                     if M.member loc m1 
                     then return (mkLets (bnds' ++ bnds_after ++ bnds) bod', env, m1'', m2'')
                     else return (mkLets (bnds' ++ loc_bnds ++ bnds_after ++ bnds) bod', env, m1'', m2'') 
            Left denv' -> cursorizeExp m1mextended m2' useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv' tenv' senv bod

        -- Exactly same as cursorizePackedExp
        LetRegionE reg sz endmut _ bod -> do
          (region_lets, freeVarToVarEnv') <- regionToBinds freeVarToVarEnv False reg sz endmut
          let reg_var = regionToVar reg
          let reg_ty = getCursorizeTyFromRegVar' Nothing useMutableCursorsCall reg_var
          let end_reg_ty = case endmut of 
                                  L2.RegionImmutable -> MkTy2 CursorTy
                                  L2.RegionMutable -> case reg_var of 
                                                           SingleR{} -> MkTy2 MutCursorTy 
                                                           SoARv{} -> reg_ty
                                                     
          reg_var_name <- case (M.lookup (fromRegVarToFreeVarsTy reg_var) freeVarToVarEnv') of
            Just var -> return var
            Nothing -> do
              case reg_var of
                SingleR v -> return v
                SoARv {} -> do
                  n <- gensym "region_cursor_ptr"
                  return n

          -- For end of the region
          reg_var_name_end <- case (M.lookup (fromRegVarToFreeVarsTy (toEndVRegVar reg_var)) freeVarToVarEnv') of
            Just var -> return var
            Nothing -> do
              case reg_var of
                SingleR v -> return $ toEndV v
                SoARv {} -> do
                  n <- gensym "region_cursor_ptr_end"
                  return n

          let freeVarToVarEnv'' = M.insert (fromRegVarToFreeVarsTy reg_var) reg_var_name freeVarToVarEnv'
          let freeVarToVarEnv''' = M.insert (fromRegVarToFreeVarsTy (toEndVRegVar reg_var)) reg_var_name_end freeVarToVarEnv''

          let tenv' = M.insert reg_var_name reg_ty tenv
          let tenv'' = M.insert reg_var_name_end end_reg_ty tenv'
          (bod, freeVarToVarEnv'''', m1', m2') <- cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv''' lenv ddfs fundefs denv tenv'' senv bod
          return (mkLets (region_lets) bod, freeVarToVarEnv'''', m1', m2') 
        LetParRegionE reg sz _ bod -> do
          -- TODO: Vidush: Do we need to pass the mut loc env etc to this call?
          (region_lets, freeVarToVarEnv') <- regionToBinds freeVarToVarEnv True reg sz L2.RegionImmutable
          (bod, freeVarToVarEnv'', m1', m2') <- cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv tenv senv bod
          return (mkLets (region_lets) bod, freeVarToVarEnv'', m1', m2') 

        {- VS: TODO: variables are not in env-}
        {- TODO: End of reg needs fixing is broken -}
        BoundsCheck i bound cur -> do
          let bound_loc = toLocVar bound
          let bound_reg = fromLocVarToRegVar bound_loc
          let bound_var = case (M.lookup (fromRegVarToFreeVarsTy bound_reg) freeVarToVarEnv) of
                Just v -> v
                Nothing -> case bound_reg of
                  SingleR vr -> vr
                  SoARv _ _ -> error $ "cursorizeExp: BoundsCheck: unexpected region variable " ++ sdoc bound_loc ++ " " ++ show freeVarToVarEnv
          let bound_var_ty = M.lookup bound_var tenv
          (additional_bnds, bound_var') <- do
            case bound_var_ty of
              Just (MkTy2 MutCursorTy) -> do
                dereference_bound_var <- gensym "deref"
                let bnd = [(dereference_bound_var, [], CursorTy, Ext $ DerefMutCursor bound_var)]
                pure (bnd, dereference_bound_var)
              Nothing -> error $ "expected variable to have type!: " ++ show bound_var
              _ -> pure ([], bound_var)
          let cur_modality = getModality cur
          let loc_seen = toLocVar cur
          let loc_seen_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy loc_seen)
          --let cur_loc = toLocVar cur
          --let cur_var = case (M.lookup (fromLocVarToFreeVarsTy cur_loc) freeVarToVarEnv) of
          ---      Just v -> v
          --      Nothing -> error $ "cursorizeExp: BoundsCheck: unexpected location variable" ++ sdoc cur_loc ++ " " ++ show freeVarToVarEnv
          (cur_loc, cur_var, additional_bnds', m1', m2') <- case fromJust cur_modality of 
                                                            L2.OutputMutable -> if M.member loc_seen m2 
                                                                             -- retrive value of the mutable location!
                                                                             then do
                                                                               let val_loc = M.lookup loc_seen m2
                                                                                 in case val_loc of 
                                                                                          Nothing -> error "Expected mut loc in env!"
                                                                                          Just (oldv, oldl, _, _) -> return (oldl, oldv, [], m1, m2)
                                                                             else do
                                                                               -- we need to dereference the mutable loction to get its value!!
                                                                               deref_var <- gensym "deref_var"
                                                                               -- wip audit, can we always just harcode cursorTy ?
                                                                               let deref_inst = (deref_var, [], CursorTy, Ext $ DerefMutCursor loc_seen_var)
                                                                               let m22 = M.insert (loc_seen) (deref_var, Nothing, Just bound_reg, S.empty) m2
                                                                               let m11 = updateMutableLocPtsToEnv loc_seen m1 (deref_var, Just loc_seen, Just bound_reg, S.empty) False
                                                                               return $ (Nothing, deref_var, [deref_inst], m11, m22)
                                                            _ -> return (Just loc_seen, loc_seen_var, [], m1, m2)
                                                             
          let mut_vars = case cur_modality of 
                                Just OutputMutable -> Just (bound_var, loc_seen_var)
                                _ -> Nothing
          let boundCheckMod = case cur_modality of 
                                    Just OutputMutable -> OutputMutable
                                    _ -> Output
          exp' <- return $ mkLets (additional_bnds ++ additional_bnds') <$> Ext $ L3.BoundsCheck i bound_var' cur_var mut_vars boundCheckMod
          -- exp' <- if isBound cur_var tenv
          --       then return $ Ext $ L3.BoundsCheck i bound_var cur_var
          --       else do
          --            let denv' = M.insertWith (++) (cur_loc) [((unwrapLocVar lvar),[],CursorTy,rhs)] denv
          --         return $ Ext $ L3.BoundsCheck i bound_var cur_var --Left$ M.insertWith (++) ((toLocVar) loc) [((unwrapLocVar lvar),[],CursorTy,rhs)] denv
          return (exp', freeVarToVarEnv, m1', m2') --m1', m2'
        Gibbon.NewL2.Syntax.BoundsCheckVector bounds -> do
          (bounds', lets, m1', m2') <-
            foldrM
              ( \(i, bound, cur) (b, l, im1, im2) -> do
                  let bound_loc = toLocVar bound
                  let bound_reg = fromLocVarToRegVar bound_loc
                  let bound_var = case (M.lookup (fromRegVarToFreeVarsTy bound_reg) freeVarToVarEnv) of
                        Just v -> v
                        Nothing -> case bound_reg of
                          SingleR vr -> vr
                          SoARv _ _ -> error $ "cursorizeExp: BoundsCheck: unexpected region variable " ++ sdoc bound_loc ++ " " ++ show freeVarToVarEnv
                  let bound_var_ty = M.lookup bound_var tenv
                  (additional_bnds, bound_var', im1', im2') <- do
                    case bound_var_ty of
                      Just (MkTy2 MutCursorTy) -> do
                        dereference_bound_var <- gensym "deref"
                        let bnd = [(dereference_bound_var, [], CursorTy, Ext $ DerefMutCursor bound_var)]
                        let im11 = updateMutableLocPtsToEnv bound_loc im1 (dereference_bound_var, Just bound_loc, Just bound_reg, S.empty) False
                        let im22 = M.insert bound_loc (dereference_bound_var, Just bound_loc, Just bound_reg, S.empty) im2
                        pure (bnd, dereference_bound_var, im11, im22)
                      Nothing -> error "expected variable to have type!"
                      _ -> pure ([], bound_var, im1, im2)
                  let cur_loc = toLocVar cur
                  let cur_var = case (M.lookup (fromLocVarToFreeVarsTy cur_loc) freeVarToVarEnv) of
                        Just v -> v
                        Nothing -> case cur_loc of
                          Single vr -> vr
                          SoA _ _ -> error $ "cursorizeExp: BoundsCheck: unexpected region variable " ++ sdoc bound_loc ++ " " ++ show freeVarToVarEnv
                  let cur_var_ty = M.lookup cur_var tenv
                  (additional_bnds', cur_var', im1'', im2'') <- do
                    case cur_var_ty of
                      Just (MkTy2 MutCursorTy) -> do
                        dereference_cur_var <- gensym "deref"
                        let bnd = [(dereference_cur_var, [], CursorTy, Ext $ DerefMutCursor cur_var)]
                        let im11 = updateMutableLocPtsToEnv cur_loc im1' (dereference_cur_var, Just cur_loc, Just bound_reg, S.empty) False
                        let im22 = M.insert cur_loc (dereference_cur_var, Just cur_loc, Just bound_reg, S.empty) im2'
                        pure (bnd, dereference_cur_var, im11, im22)
                      Nothing -> error "expected variable to have type!"
                      _ -> pure ([], cur_var, im1', im2')
                  return (b ++ [(i, bound_var', cur_var', (bound_var, cur_var))], l ++ additional_bnds ++ additional_bnds', im1'', im2'')
              )
              ([], [], m1, m2)
              bounds
          let end_regs = map (\(_, bound, _) _ -> let bound_loc = toLocVar bound
                                                      bound_reg = fromLocVarToRegVar bound_loc
                                                    in bound_reg
                             ) bounds
          -- Now i need to find the parent region of these single regs. 
          -- Update these regions in the parent 
          -- and propgate the new region in the environment.    
          exp' <- return $ mkLets lets <$> Ext $ L3.BoundsCheckVector bounds'
          return (exp', freeVarToVarEnv, m1', m2')
        FromEndE {} -> error $ "cursorizeExp: TODO FromEndE" ++ sdoc ext
        IndirectionE {} -> error $ "cursorizeExp: Unexpected IndirectionE"
        GetCilkWorkerNum -> return (Ext $ L3.GetCilkWorkerNum, freeVarToVarEnv, m1, m2)
        LetAvail vs bod -> do
                            (bod', env, m1', m2') <- go insideTimeIt m1 m2 freeVarToVarEnv bod
                            return (Ext $ L3.LetAvail vs bod', env, m1', m2') 
        AllocateTagHere varg tycon -> do
          case (isMutModality $ fromJust $ getModality varg) of
            False -> do  
                     let v = toLocVar varg
                     let variable_name = case (M.lookup (fromLocVarToFreeVarsTy v) freeVarToVarEnv) of
                                              Just v -> v
                                              Nothing -> error "cursorizeExp: AllocateTagHere: unexpected location variable"
                     pure (Ext $ L3.AllocateTagHere (variable_name) tycon, freeVarToVarEnv, m1, m2)
            True -> do
                    -- see where this mutable location points to. 
                    -- if the env is empty, we will need to dereference the location to get its value.
                    let v = toLocVar varg
                    case (M.member v m2) of 
                           True -> case (M.lookup v m2) of 
                                             Nothing ->  error "Expected to have associated value!"
                                             Just (v', l, _, _) -> let 
                                                             exp = Ext $ L3.AllocateTagHere v' tycon
                                                            in pure (exp, freeVarToVarEnv, m1, m2)
                           False -> error "Not implemented!!"

        AllocateScalarsHere varg -> do
          case (isMutModality $ fromJust $ getModality varg) of 
            False -> do 
                      let v = toLocVar varg
                      let variable_name = case (M.lookup (fromLocVarToFreeVarsTy v) freeVarToVarEnv) of
                                                  Just v -> v
                                                  Nothing -> error "cursorizeExp: AllocateTagHere: unexpected location variable"
                      pure (Ext $ L3.AllocateScalarsHere (variable_name), freeVarToVarEnv, m1, m2)

            True -> do 
                     let v = toLocVar varg 
                     case (M.lookup v m2) of 
                            Nothing -> error "Not implemented!!"
                            Just (v', l, _, _) -> let 
                                              exp = Ext $ L3.AllocateScalarsHere v'
                                             in pure (exp, freeVarToVarEnv, m1, m2)

        SSPush a b c d -> pure (Ext $ L3.SSPush a (unwrapLocVar b) (unwrapLocVar c) d, freeVarToVarEnv, m1, m2)
        SSPop a b c -> pure (Ext $ L3.SSPop a (unwrapLocVar b) (unwrapLocVar c), freeVarToVarEnv, m1, m2)
        {-VS: TODO: This needs to be fixed to produce the correct L3 expression. See above. -}
        {- Right now i just skip the let region, just recurse on the body-}
        LetRegE loca rhs bod -> do
          -- let loc = fromRegVarToLocVar reg_var
          -- VS: Hack, assume that these are always Mutable cursors.
          -- TODO: We should have a pass to decide what we should make mutable
          -- vs: what we should not not make mutable.
          -- let ty_of_loc = case loc of
          --                   SingleR _ -> CursorTy
          --                   SoARv _ flds -> CursorArrayTy (1 + length flds)
          -- let ty2_of_loc :: Ty2 = case loc of
          --                           SingleR _ -> MkTy2 CursorTy
          --                           SoARv _ flds -> MkTy2 $ CursorArrayTy (1 + length flds)
          -- In case we unpack single regions, we make them mutable since they may
          -- be updated by bounds check.
          let loc = fromLocVarToRegVar $ toLocVar loca
          let modality = getModality loca
          let ty_of_loc = getCursorizeTyFromRegVar'' modality useMutableCursorsCall loc
          let ty2_of_loc :: Ty2 = getCursorizeTyFromRegVar' modality useMutableCursorsCall loc
          freeVarToVarEnv' <- do
            case loc of
              SingleR l ->
                if M.member (fromRegVarToFreeVarsTy loc) freeVarToVarEnv
                  then return freeVarToVarEnv
                  else return $ M.insert (fromRegVarToFreeVarsTy loc) l freeVarToVarEnv
              SoARv _ _ -> case (isMutModality (fromJust modality)) of 
                  True -> pure freeVarToVarEnv
                  False -> if (M.member (fromRegVarToFreeVarsTy loc) freeVarToVarEnv)
                            -- overwrite this location with a new variable
                           then do
                              name <- gensym "overwrite_reg" 
                              return $ M.insert (fromRegVarToFreeVarsTy loc) name freeVarToVarEnv
                           else do
                              name <- gensym "cursor_ptr"
                              return $ M.insert (fromRegVarToFreeVarsTy loc) name freeVarToVarEnv 
          (rhs_either, m1', m2') <- dbgTrace (minChatLvl) "Print the type of the Region: " dbgTrace (minChatLvl) (sdoc (ty2_of_loc, ty2_of_loc, modality)) dbgTrace (minChatLvl) "End printing the region!\n" cursorizeRegExp m1 m2 useMutableCursorsCall freeVarToVarEnv' denv tenv senv loc rhs
          let (bnds, tenv') = case M.lookup (fromRegVarToFreeVarsTy loc) denv of
                Nothing -> ([], tenv)
                Just vs ->
                  let extended = M.fromList [(v, MkTy2 CursorTy) | (v, _, CursorTy, _) <- vs]
                   in (vs, M.union extended tenv)
          case rhs_either of
            Right (rhs', bnds', tenv'', senv') -> do
              let tenv''' = M.union tenv' tenv''
              let locs_var = case (M.lookup (fromRegVarToFreeVarsTy loc) freeVarToVarEnv') of
                    Just v -> v
                    Nothing -> case loc of
                      SingleR lvarrr -> lvarrr
                      SoARv _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
              case rhs of
                -- Discharge bindings that were waiting on 'loc'.
                _ -> case ty_of_loc of
                  MutCursorTy -> do
                       (bod', env, m1'', m2'') <- cursorizeExp m1' m2' useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv (M.insert locs_var (ty2_of_loc) tenv''') senv' bod
                       return (mkLets (bnds' ++ [(locs_var, [], ty_of_loc, Ext $ AddrOfCursor rhs')] ++ bnds) bod', env, m1'', m2'')
                  _ -> do
                       (bod', env, m1'', m2'') <- cursorizeExp m1' m2' useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv (M.insert locs_var (ty2_of_loc) tenv''') senv' bod
                       case modality of 
                            -- Getting rid of overwritten regions, in OutputMutable mode.
                            -- Vidush: Audit, is this correct way to handle this?
                            Just OutputMutable -> return (mkLets (bnds' ++ bnds) bod', env, m1'', m2'')  
                            _ -> return (mkLets (bnds' ++ [(locs_var, [], ty_of_loc, rhs')] ++ bnds) bod', env, m1'', m2'')
            -- cursorizeExp freeVarToVarEnv' lenv ddfs fundefs denv (M.insert locs_var (MkTy2 ty2_of_loc) tenv''') senv' bod
            Left denv' -> do
                          (bod', env, m1'', m2'') <- cursorizeExp m1' m2' useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv' tenv' senv bod
                          return ((mkLets bnds) bod', env, m1'', m2'')
        -- case reg_var of
        -- SingleR v -> cursorizePackedExp freeVarToVarEnv ddfs fundefs denv tenv senv bod
        -- SoARv dv _ -> cursorizePackedExp freeVarToVarEnv ddfs fundefs denv tenv senv bod

    MapE {} -> error $ "TODO: cursorizeExp MapE"
    FoldE {} -> error $ "TODO: cursorizeExp FoldE"
  where
    go insidetimeit gm1 gm2 fenv = cursorizeExp gm1 gm2 useMutableCursorsCall emitScalarCountBumps insidetimeit fenv lenv ddfs fundefs denv tenv senv

insertRegInVarEnv :: RegVar -> M.Map FreeVarsTy Var -> PassM (M.Map FreeVarsTy Var)
insertRegInVarEnv reg_var env = do
  case reg_var of
    SingleR l ->
      if M.member (fromRegVarToFreeVarsTy reg_var) env
        then return env
        else return $ M.insert (fromRegVarToFreeVarsTy reg_var) l env
    SoARv _ _ ->
      if M.member (fromRegVarToFreeVarsTy reg_var) env
        then return $ env
        else do
          name <- gensym "reg_cursor_ptr"
          return $ M.insert (fromRegVarToFreeVarsTy reg_var) name env

insertLocInVarEnv :: LocVar -> M.Map FreeVarsTy Var -> PassM (M.Map FreeVarsTy Var)
insertLocInVarEnv loc env = do
  case loc of
    Single l ->
      if M.member (fromLocVarToFreeVarsTy loc) env
        then return env
        else return $ M.insert (fromLocVarToFreeVarsTy loc) l env
    SoA _ _ ->
      if M.member (fromLocVarToFreeVarsTy loc) env
        then return $ env
        else do
          name <- gensym "loc_cursor_ptr"
          return $ M.insert (fromLocVarToFreeVarsTy loc) name env

-- Cursorize expressions producing `Packed` values
unitizePackedMutableResult :: Ty2 -> Exp3 -> Exp3
unitizePackedMutableResult ty ex =
  case unTy2 ty of
    PackedTy{} ->
      case ex of
        LetE b bod -> LetE b (unitizePackedMutableResult ty bod)
        IfE a b c -> IfE a (unitizePackedMutableResult ty b) (unitizePackedMutableResult ty c)
        AppE{} -> LetE ("_", [], ProdTy [], ex) (MkProdE [])
        _ -> MkProdE []
    ProdTy tys ->
      case ex of
        LetE b bod -> LetE b (unitizePackedMutableResult ty bod)
        IfE a b c -> IfE a (unitizePackedMutableResult ty b) (unitizePackedMutableResult ty c)
        MkProdE es | length es == length tys ->
          MkProdE (zipWith unitizePackedMutableField tys es)
        _ ->
          MkProdE (zipWith (\i t -> unitizePackedMutableField t (mkProj i ex)) [0..] tys)
    _ -> ex
  where
    unitizePackedMutableField fieldTy fieldExp =
      case fieldTy of
        PackedTy{} -> unitizePackedMutableResult (MkTy2 fieldTy) fieldExp
        ProdTy{} -> unitizePackedMutableResult (MkTy2 fieldTy) fieldExp
        _ -> fieldExp

unitizedPackedMutableTy :: Ty2 -> Ty3
unitizedPackedMutableTy ty =
  stripTyLocs $
    case mapPacked (\_ _ -> ProdTy []) (unTy2 ty) of
      SymDictTy a _ -> SymDictTy a CursorTy
      ty' -> ty'

mutableLocLetPayload :: Ty2 -> Exp3 -> Exp3
mutableLocLetPayload ty ex =
  case ex of
    LetE b@(v, _, _, rhs) bod ->
      case rhs of
        AppE{} -> LetE b (unitizePackedMutableResult ty (VarE v))
        _ -> LetE b (mutableLocLetPayload ty bod)
    IfE a b c -> IfE a (mutableLocLetPayload ty b) (mutableLocLetPayload ty c)
    _ -> unitizePackedMutableResult ty ex

bindMutableLetLoc :: LocVar -> LocArg -> Var -> Exp3 -> MutableLocOldValueEnv -> PassM ([Binds Exp3], MutableLocOldValueEnv)
bindMutableLetLoc loc locarg locsVar rhs mutOldVals =
  case rhs of
    Ext (AddrOfCursor cursorExp) -> do
      (cursorVar, cursorBnds) <- case cursorExp of
        VarE var -> pure (var, [])
        _ -> do
          locCur <- gensym "loc_cursor"
          pure (locCur, [(locCur, [], CursorTy, cursorExp)])
      let oldEntry = oldMutableLetLocEntry cursorVar
      pure (cursorBnds ++ [(locsVar, [], MutCursorTy, Ext $ AddrOfCursor (VarE cursorVar))], M.insert loc oldEntry mutOldVals)
    _ -> do
      locCur <- gensym "loc_cursor"
      let oldEntry = oldMutableLetLocEntry locCur
      pure ([(locCur, [], CursorTy, rhs), (locsVar, [], MutCursorTy, Ext $ AddrOfCursor (VarE locCur))], M.insert loc oldEntry mutOldVals)
  where
    oldMutableLetLocEntry cursorVar =
      case M.lookup loc mutOldVals of
        Just (_, oldloc, ereg, aliases) -> (cursorVar, oldloc, ereg, aliases)
        Nothing -> (cursorVar, Just loc, Just (toEndRegVar locarg), S.empty)

cursorValueFromMaybeMut :: TyEnv Var Ty2 -> Var -> Exp3
cursorValueFromMaybeMut tenv var =
  case M.lookup var tenv of
    Just ty | unTy2 ty == CursorTy -> VarE var
    Just ty | unTy2 ty == MutCursorTy -> Ext $ DerefMutCursor var
    _ -> VarE var

isGeneratedSoAFieldVar :: Var -> Bool
isGeneratedSoAFieldVar var = "soa_field_" `L.isPrefixOf` fromVar var

cursorValueFromMaybeTrackedMut :: MutableLocPtsToEnv -> TyEnv Var Ty2 -> Var -> Exp3
cursorValueFromMaybeTrackedMut m1 tenv var =
  case M.lookup var tenv of
    Just ty | unTy2 ty == CursorTy && isGeneratedSoAFieldVar var -> Ext $ DerefMutCursor var
    Just ty | unTy2 ty == CursorTy -> VarE var
    Just ty | unTy2 ty == MutCursorTy -> Ext $ DerefMutCursor var
    Just _ -> VarE var
    Nothing | isGeneratedSoAFieldVar var -> Ext $ DerefMutCursor var
    Nothing -> VarE var

cursorizePackedExp ::
  MutableLocPtsToEnv ->
  MutableLocOldValueEnv ->
  Bool ->
  Bool ->
  Bool ->
  M.Map FreeVarsTy Var ->
  M.Map Var (Maybe LocVar) ->
  DDefs Ty2 ->
  FunDefs2 ->
  DepEnv ->
  TyEnv Var Ty2 ->
  SyncEnv ->
  Exp2 ->
  PassM (DiExp Exp3, M.Map FreeVarsTy Var, MutableLocPtsToEnv, MutableLocOldValueEnv)
cursorizePackedExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv ddfs fundefs denv tenv senv ex =
  case ex of
    -- Here the allocation has already been performed:
    -- To follow the calling convention, we are reponsible for tagging on the
    -- end here:
    VarE v -> do
      let ty = case M.lookup v tenv of
            Just t -> t
            Nothing -> error $ sdoc v ++ " not found."
      case (unTy2 ty) of
        PackedTy _ l ->
                        if (M.member l m1) && useMutableCursorsCall
                        then return (dl $ L3.MkProdE [], freeVarToVarEnv, m1, m2)
                        else return (mkDi (VarE v) [VarE (toEndV v)], freeVarToVarEnv, m1, m2)
        _ -> return (dl $ VarE v, freeVarToVarEnv, m1, m2)
    LitE _n -> error $ "Shouldn't encounter LitE in packed context:" ++ sdoc ex
    CharE _n -> error $ "Shouldn't encounter CharE in packed context:" ++ sdoc ex
    FloatE {} -> error $ "Shouldn't encounter FloatE in packed context:" ++ sdoc ex
    LitSymE _n -> error $ "Shouldn't encounter LitSymE in packed context:" ++ sdoc ex
    AppE {} -> do
               (ex', freeVarToVarEnv', m1', m2') <- cursorizeAppE m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv ddfs fundefs denv tenv senv ex
               return (dl ex', freeVarToVarEnv', m1', m2')
    -- DictLookup returns a packed value bound to a free location.
    -- PrimAppE (DictLookupP (PackedTy _ ploc)) vs ->
    --     do vs' <- forM vs $ \v -> cursorizeExp ddfs fundefs denv tenv v
    --        return $ mkDi (PrimAppE (DictLookupP CursorTy) vs') [ Ext NullCursor ]

    PrimAppE _ _ -> error $ "cursorizePackedExp: unexpected PrimAppE in packed context:" ++ sdoc ex
    -- The only (other) primitive that returns packed data is ReadPackedFile:
    -- This is simpler than TimeIt below.  While it's out-of-line,
    -- it doesn't need memory allocation (NewBuffer/ScopedBuffer).
    -- This is more like the witness case below.
    LetE (v, _locs, _ty, (PrimAppE (ReadPackedFile path tyc reg ty2) [])) bod -> do
      (bod', freeVarToVarEnv', m1', m2') <- cursorizeReadPackedFile m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv ddfs fundefs denv tenv senv True v path tyc reg ty2 bod
      return (Di bod', freeVarToVarEnv', m1', m2') 
    LetE (v, _locs, _ty, (PrimAppE (DictLookupP (MkTy2 (PackedTy _ ploc))) vs)) bod ->
      do
        vs' <- forM vs $ \w -> cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv ddfs fundefs denv tenv senv w
        let vs'' = map (\(a, _, _, _) -> a) vs'
        let envs' = map (\(_, b, _, _) -> b) vs'
        let m1s' = map (\(_, _, c, _) -> c) vs'
        let m2s' = map (\(_, _, _, d) -> d) vs'
        let bnd =
              mkLets
                [ ((unwrapLocVar ploc), [], CursorTy, (PrimAppE (DictLookupP CursorTy) vs'')),
                  (v, [], CursorTy, VarE (unwrapLocVar ploc))
                ]
            tenv' = M.insert (unwrapLocVar ploc) (MkTy2 CursorTy) $ M.insert v (MkTy2 CursorTy) tenv
        (bod', freeVarToVarEnv', m1', m2') <- go insideTimeit m1 m2 freeVarToVarEnv tenv' senv bod
        return (onDi bnd bod', M.unions $ [freeVarToVarEnv'] ++ envs', M.unions (m1s' ++ [m1]), M.unions (m2s' ++ [m2]))

    LetE (_v, _locs, _ty, (MkProdE _ls)) _bod -> do
      (ex', freeVarToVarEnv', m1', m2') <- cursorizeProd m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv True ddfs fundefs denv tenv senv ex
      return (dl ex', freeVarToVarEnv', m1', m2') 
    LetE (_v, _locs, ty, ProjE {}) _bod
      | isPackedTy (unTy2 ty) -> do
          (ex', freeVarToVarEnv', m1', m2') <- cursorizeProj m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv True ddfs fundefs denv tenv senv ex
          return (dl ex', freeVarToVarEnv', m1', m2') 
    MkProdE ls -> do
      let tys = L.map (gRecoverType ddfs (Env2 tenv M.empty)) ls
      res <- 
        forM (zip tys ls) $ \(ty, e) -> do
          case ty of
            _ | isPackedTy (unTy2 ty) -> do 
                                        (e', freeVarToVarEnv', m1', m2') <- cursorizePackedExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv ddfs fundefs denv tenv senv e
                                        return (fromDi e', freeVarToVarEnv', m1', m2') 
            _ -> cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv ddfs fundefs denv tenv senv e
      let es = map fst4 res
      let envs = map snd4 res
      let m1s' = map thd4 res
      let m2s' = map fth4 res
      let rhs' = MkProdE es
      return (Di rhs', M.unions envs, M.unions (m1s' ++ [m1]), M.unions (m2s' ++ [m2]))

    -- Not sure if we need to replicate all the checks from Cursorize1
    ProjE i e -> do 
                 (e', env, m1', m2') <- go insideTimeit m1 m2 freeVarToVarEnv tenv senv e 
                 return (dl $ ProjE i (fromDi e'), env, m1', m2') 
    LetE (_v, _locs, _ty, SpawnE {}) _bod -> do 
      (ex', freeVarToVarEnv', m1', m2') <- cursorizeSpawn m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv True ddfs fundefs denv tenv senv ex
      return (dl ex', freeVarToVarEnv', m1', m2') 
    LetE (_v, _locs, _ty, SyncE) _bod -> do
      (ex', freeVarToVarEnv', m1', m2') <- cursorizeSync m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv True ddfs fundefs denv tenv senv ex
      return (dl ex', freeVarToVarEnv', m1', m2') 
    LetE (v, _locs, ty, rhs@(Ext (SSPush _ start _ _))) bod ->
      case M.lookup (unwrapLocVar start) tenv of
        Nothing -> go insideTimeit m1 m2 freeVarToVarEnv tenv senv bod
        Just {} -> do
          (rhs', env1, m1', m2') <- go insideTimeit m1 m2 freeVarToVarEnv tenv senv rhs
          let ty' = cursorizeTy freeVarToVarEnv m1' m2' useMutableCursorsCall Nothing (unTy2 ty)
          (bod', env2, m1'', m2'') <- go insideTimeit m1' m2' freeVarToVarEnv (M.insert v ty tenv) senv bod
          return (Di (LetE (v, [], ty', fromDi rhs') (fromDi bod')), M.union env1 env2, m1'', m2'') 
    LetE (v, _locs, ty, rhs@(Ext (SSPop _ start _))) bod ->
      case M.lookup (unwrapLocVar start) tenv of
        Nothing -> go insideTimeit m1 m2 freeVarToVarEnv tenv senv bod
        Just {} -> do
          (rhs', env1, m1', m2') <- go insideTimeit m1 m2 freeVarToVarEnv tenv senv rhs
          let ty' = cursorizeTy freeVarToVarEnv m1' m2' useMutableCursorsCall Nothing (unTy2 ty)
          (bod', env2, m1'', m2'') <- go insideTimeit m1' m2' freeVarToVarEnv (M.insert v ty tenv) senv bod
          return (Di (LetE (v, [], ty', fromDi rhs') (fromDi bod')), M.union env1 env2, m1'', m2'')
    LetE bnd@(_, _locs, _, _) bod -> do
      freeVarToVarEnv' <-
        foldrM
          ( \loc env -> case loc of
              EndOfReg r _ er -> do
                env' <- insertRegInVarEnv r env
                env'' <- insertRegInVarEnv er env'
                return env''
              EndWitness lrem loc -> do
                env' <- insertLocInVarEnv loc env
                env'' <- insertLocInVarEnv (lremLoc lrem) env'
                env''' <- insertRegInVarEnv (lremEndReg lrem) env''
                env'''' <- insertRegInVarEnv (lremReg lrem) env'''
                return env''''
              Loc lrem -> do
                env' <- insertLocInVarEnv (lremLoc lrem) env
                env'' <- insertRegInVarEnv (lremEndReg lrem) env'
                env''' <- insertRegInVarEnv (lremReg lrem) env''
                return env'''
              Reg r _ -> do
                env' <- insertRegInVarEnv r env
                return env'
              EndOfReg_Tagged r -> do
                env' <- insertRegInVarEnv r env
                return env'
          )
          freeVarToVarEnv
          _locs
      (bod', freeVarToVarEnv'', m1', m2') <- cursorizeLet m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv' lenv True ddfs fundefs denv tenv senv bnd bod
      return (dl bod', freeVarToVarEnv'', m1', m2') 

    -- Here we route the dest cursor to both braches.  We switch
    -- back to the other mode for the (non-packed) test condition.
    IfE a b c -> do
      (Di b', env1, m1', m2') <- go insideTimeit m1 m2 freeVarToVarEnv tenv senv b
      (Di c', env2, m1'', m2'') <- go insideTimeit m1 m2 freeVarToVarEnv tenv senv c
      (a', env3, m1''', m2''') <- cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv ddfs fundefs denv tenv senv a
      let m1'''' = M.unions [m1', m1'', m1''']
      let m2'''' = M.unions [m2', m2'', m2''']
      let branchTy = gRecoverType ddfs (Env2 tenv M.empty) b
          b_unit = if useMutableCursorsCall then unitizePackedMutableResult branchTy b' else b'
          c_unit = if useMutableCursorsCall then unitizePackedMutableResult branchTy c' else c'
      return (Di $ IfE a' b_unit c_unit, M.unions [env1, env2, env3], m1'''', m2'''')

    -- A case expression is eventually transformed into a ReadTag + switch stmt.
    -- We first retrieve the cursor referred to by the scrutinee, and unpack
    -- the first bound variable 1 byte after that cursor. Thats all we need to do
    -- here, because we've already computed other locations in InferLocations and
    -- RouteEnds
    CaseE scrt brs -> do
      -- ASSUMPTION: scrutinee is always flat
      let (VarE v) = scrt

      freeVarToVarEnv' <-
        foldrM
          ( \(dcon, vlocs, rhs) acc -> do
              case vlocs of
                [] -> return acc
                _ -> do
                  acc' <-
                    foldrM
                      (\(v, l) acc'' -> do
                          case (toLocVar l) of
                            Single l' -> return $ M.insert (fromLocVarToFreeVarsTy (toLocVar l)) l' acc''
                            SoA _ _ -> do
                              if M.member (fromLocVarToFreeVarsTy (toLocVar l)) acc''
                                then return acc''
                                else do
                                  name <- gensym "cursor_ptr"
                                  return $ M.insert (fromLocVarToFreeVarsTy (toLocVar l)) name acc''
                      )
                      acc
                      vlocs
                  return acc'
          )
          freeVarToVarEnv
          brs
      let ty_of_scrut = case (M.lookup v tenv) of
            Just (MkTy2 ty) -> ty
            Nothing -> error "unpackDataCon: unexpected location variable"
      dcon_var <- gensym "dcon"
      let scrutMutable = checkIfVarIsMutable v m1
      {-VS: TODO: get location of scrutinee, send it to unpack data con. Get the L2 location!!!-}
      -- Don't think we need this for now.
      -- (dcon_var, dcon_let_bind) <- case scrutMutable of 
      --                                               True -> do 
      --                                                       dcon_var <- gensym "dcon"
      --                                                       dcon_deref <- gensym "deref_dcon"
      --                                                       let dcon_let = [(dcon_var, [], MutCursorTy, Ext $ AddrOfCursor $ Ext $ IndexCursorArray v 0)]
      --                                                       let deref_dcon = [(dcon_deref, [], CursorTy, Ext $ DerefMutCursor dcon_var)]
      --                                                       let dcon_let_bind = mkLets $ dcon_let ++ deref_dcon
      --                                                       return (dcon_deref, dcon_let_bind)
      --                                               False -> do 
      --                                                        dcon_var <- gensym "dcon"
      --                                                        let dcon_let = [(dcon_var, [], CursorTy, Ext $ IndexCursorArray v 0)]
      --                                                        let dcon_let_bind = mkLets dcon_let
      --                                                        return (dcon_var, dcon_let_bind)
      let all_buffers_alive =
            S.fromList
              [ (dcon, idx)
              | (dcon, var_locs, _) <- brs,
                idx <- [0 .. length var_locs - 1]
              ]
      let vars_mentioned = varsMentionedInExp ex
      let alive_buffers =
            if isNoDeadFieldElim denv
              then all_buffers_alive
              else
                foldr
                  ( \(dcon, var_locs, _) acc ->
                      foldr
                        (\(idx, (var, _)) acc' -> if S.member var vars_mentioned then S.insert (dcon, idx) acc' else acc')
                        acc
                        (zip [0 ..] var_locs)
                  )
                  S.empty
                  brs
      --let alive_buffers = S.empty
      case ty_of_scrut of
        CursorTy -> (,,,) <$> (dl <$> CaseE (VarE $ v))
                          <$> mapM (unpackDataCon alive_buffers m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv senv True v) brs
                    <*> dbgTrace (minChatLvl) "Print in Cursor Case: " dbgTrace (minChatLvl) (sdoc (ty_of_scrut, v, alive_buffers)) dbgTrace (minChatLvl) "End print in Cursor Case.\n" return freeVarToVarEnv 
                    <*> return m1
                    <*> return m2
        -- We need to dereference a mutable cursor to get its value.
        MutCursorTy -> do
                       deref_val <- gensym "deref_val"
                       let additional_deref_let = mkLets [(deref_val, [], CursorTy, Ext $ DerefMutCursor v)]
                       let tenv' = M.insert deref_val (MkTy2 CursorTy) tenv
                       let output_mut_loc_scrut = dbgTrace (minChatLvl) "Print in MutCursor Case: " dbgTrace (minChatLvl) (sdoc (ty_of_scrut, v, alive_buffers)) dbgTrace (minChatLvl) "End print in MutCursor Case.\n" findMutableLocationPointingToVar v m1
                       (m1', m2') <- case output_mut_loc_scrut of 
                                            Nothing -> error "Did not expect mutable cursor!\n"
                                            Just outloc -> do let m1i = updateMutableLocPtsToEnv outloc m1 (deref_val, Just outloc, Nothing, S.empty) False 
                                                              let m2i = M.insert outloc (deref_val, Just outloc, Nothing, S.empty) m2
                                                              return (m1i, m2i)
                       (,,,) <$> (dl <$> additional_deref_let <$> CaseE (VarE $ deref_val))
                                        <$> mapM (unpackDataCon alive_buffers m1' m2' useMutableCursorsCall emitScalarCountBumps insideTimeit dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv' senv True deref_val) brs
                                  <*> return freeVarToVarEnv 
                                  <*> return m1'
                                  <*> return m2'
        
        CursorArrayTy {} -> do
            -- check if v points to any mutable location
            let mut_loc_pointing_to_v = findMutableLocationPointingToVar v m1
            (dcon_var', dcon_let, m1', m2', freeVarToVarEnv'') <- case mut_loc_pointing_to_v of 
                                                            Nothing -> do 
                                                                       let dcon_let_bind = [(dcon_var, [], CursorTy, Ext $ IndexCursorArray v 0)]
                                                                       dbgTrace (minChatLvl) "Print in case Cursor ArrayTy: " dbgTrace (minChatLvl) (sdoc (mut_loc_pointing_to_v, v, alive_buffers)) dbgTrace (minChatLvl) "End in print case Nothing cursor array ty.\n" return (dcon_var, dcon_let_bind, m1, m2, freeVarToVarEnv')
                                                            Just ml -> do
                                                                        dcon_var_deref <- gensym "deref_dcon_var"
                                                                        let dcon_loc = getDconLoc ml
                                                                        let (dcon_loc_name, freeVarToVarEnv_i) = if M.member (fromLocVarToFreeVarsTy dcon_loc) freeVarToVarEnv' 
                                                                                                                 then (getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy dcon_loc), freeVarToVarEnv')
                                                                                                                 else case dcon_loc of 
                                                                                                                        Single l -> (l, M.insert (fromLocVarToFreeVarsTy dcon_loc) l freeVarToVarEnv')   
                                                                                                                        SoA{} -> error "Did not expect SoA location for data constructor region!\n"
                                                                        let dcon_let_bind = [(dcon_loc_name, [], MutCursorTy, Ext $ AddrOfCursor $ Ext $ IndexCursorArray v 0)]
                                                                        let m1i = updateMutableLocPtsToEnv dcon_loc m1 (dcon_var_deref, Just dcon_loc, Nothing, S.empty) True
                                                                        let m2i = M.insert dcon_loc (dcon_var_deref, Just dcon_loc, Nothing, S.empty) m2
                                                                        let deref_dcon_mut = [(dcon_var_deref, [], CursorTy, Ext $ DerefMutCursor dcon_loc_name)]
                                                                        dbgTrace (minChatLvl) "Print in case Cursor ArrayTy: " dbgTrace (minChatLvl) (sdoc (mut_loc_pointing_to_v, v, alive_buffers)) dbgTrace (minChatLvl) "End in print case Just ml cursor array ty.\n" return (dcon_var_deref, (dcon_let_bind ++ deref_dcon_mut), m1i, m2i, freeVarToVarEnv_i)
            let dcon_let_bind = mkLets dcon_let
            (,,,) <$> dl
              <$> dcon_let_bind
              <$> CaseE (VarE $ dcon_var')
              <$> mapM (unpackDataCon alive_buffers m1' m2' useMutableCursorsCall emitScalarCountBumps insideTimeit dcon_var' freeVarToVarEnv'' lenv ddfs fundefs denv tenv senv True v) brs
              <*> return freeVarToVarEnv'' 
              <*> return m1' 
              <*> return m2'
        
        PackedTy _ scrutLoc -> case scrutLoc of
          Single _ -> (,,,) <$> dl
                        <$> CaseE (VarE $ v)
                        <$> mapM (unpackDataCon alive_buffers m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv senv True v) brs
                      <*> return freeVarToVarEnv
                      <*> return m1
                      <*> return m2
          
          SoA _ _ -> do
              -- check if v points to any mutable location
              let mut_loc_pointing_to_v = findMutableLocationPointingToVar v m1
              (dcon_var', dcon_let, m1', m2', freeVarToVarEnv'') <- case mut_loc_pointing_to_v of 
                                                            Nothing -> do 
                                                                       let dcon_let_bind = [(dcon_var, [], CursorTy, Ext $ IndexCursorArray v 0)]
                                                                       dbgTrace (minChatLvl) "Print in case Cursor ArrayTy: " dbgTrace (minChatLvl) (sdoc (mut_loc_pointing_to_v, v)) dbgTrace (minChatLvl) "End in print case Nothing cursor array ty.\n" return (dcon_var, dcon_let_bind, m1, m2, freeVarToVarEnv')
                                                            Just ml -> do
                                                                        dcon_var_deref <- gensym "deref_dcon_var"
                                                                        let dcon_loc = getDconLoc ml
                                                                        let (dcon_loc_name, freeVarToVarEnv_i) = if M.member (fromLocVarToFreeVarsTy dcon_loc) freeVarToVarEnv' 
                                                                                                                 then (getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy dcon_loc), freeVarToVarEnv')
                                                                                                                 else case dcon_loc of 
                                                                                                                        Single l -> (l, M.insert (fromLocVarToFreeVarsTy dcon_loc) l freeVarToVarEnv')   
                                                                                                                        SoA{} -> error "Did not expect SoA location for data constructor region!\n"
                                                                        let dcon_let_bind = [(dcon_loc_name, [], MutCursorTy, Ext $ AddrOfCursor $ Ext $ IndexCursorArray v 0)]
                                                                        let m1i = updateMutableLocPtsToEnv dcon_loc m1 (dcon_var_deref, Just dcon_loc, Nothing, S.empty) True
                                                                        let m2i = M.insert dcon_loc (dcon_var_deref, Just dcon_loc, Nothing, S.empty) m2
                                                                        let deref_dcon_mut = [(dcon_var_deref, [], CursorTy, Ext $ DerefMutCursor dcon_loc_name)]
                                                                        dbgTrace (minChatLvl) "Print in case Cursor ArrayTy: " dbgTrace (minChatLvl) (sdoc (mut_loc_pointing_to_v, v)) dbgTrace (minChatLvl) "End in print case Just ml cursor array ty.\n" return (dcon_var_deref, (dcon_let_bind ++ deref_dcon_mut), m1i, m2i, freeVarToVarEnv_i)
              let dcon_let_bind = mkLets dcon_let
              (,,,) <$> dl
                <$> dcon_let_bind
                <$> CaseE (VarE $ dcon_var')
                <$> mapM (unpackDataCon alive_buffers m1' m2' useMutableCursorsCall emitScalarCountBumps insideTimeit dcon_var' freeVarToVarEnv'' lenv ddfs fundefs denv tenv senv True v) brs
                <*> return freeVarToVarEnv''
                <*> return m1'
                <*> return m2'

        _ ->
            (,,,) <$> dl
            <$> CaseE (VarE $ v)
            <$> mapM (unpackDataCon alive_buffers m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit dcon_var freeVarToVarEnv' lenv ddfs fundefs denv tenv senv True v) brs
            <*> return freeVarToVarEnv
            <*> return m1
            <*> return m2
    
    DataConE slocarg dcon args -> do
      if (not (isSoALoc (toLocVar slocarg)))
        then do
          let sloc_loc = toLocVar slocarg
              modality_sloc = getModality slocarg
              -- check if sloc is an output mutable location.
          (sloc_loc_to_write, sloc, additional_bnds) <- if isMutModality $ fromJust modality_sloc
                                                        -- check the old modality environment to get the old value of the mutable location
                                                        then 
                                                          case M.lookup sloc_loc m2 of
                                                              -- Vidush: Rather then erroring out, we may want to de-reference the mutable loc here
                                                              Nothing -> do 
                                                                  deref_val <- gensym "deref_val"
                                                                  let sloc_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy sloc_loc)
                                                                  let deref_let  = [(deref_val, [], CursorTy, Ext $ DerefMutCursor sloc_var)]
                                                                  return (Just sloc_loc, deref_val, deref_let)
                                                                  -- error $ "expected to have old value for the output mutable location!" ++ show (sloc_loc, dcon, deref_let) 
                                                              Just (oldv, oldl, _, _) -> case oldl of 
                                                                                              Nothing -> return (Nothing, oldv, [])
                                                                                              Just ol -> return (Just ol, oldv, [])
                                                        else return (Just sloc_loc, getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy sloc_loc), []) 
          let m1_dcon = if isMutModality $ fromJust modality_sloc
                        then case M.lookup sloc_loc m1 of
                               Nothing -> updateMutableLocPtsToEnv sloc_loc m1 (sloc, Just sloc_loc, Nothing, S.empty) False
                               Just{} -> m1
                        else m1
              -- sloc = case (M.lookup (fromLocVarToFreeVarsTy sloc_loc) freeVarToVarEnv) of
              --   Just v -> v
              --   Nothing -> error $ "cursorizeExp(988): DataConE: unexpected location variable" ++ "(" ++ show sloc_loc ++ ")" ++ show freeVarToVarEnv
              -- Return (start,end) cursors
              -- The final return value lives at the position of the out cursors:
          let go2 ::  MutableLocPtsToEnv -> MutableLocOldValueEnv -> Bool -> Var -> [(Exp2, Ty2)] -> PassM (Exp3,  MutableLocPtsToEnv, MutableLocOldValueEnv)
              go2 mg1 mg2 marker_added d [] = do
                let red_prod = if isMutModality $ fromJust $ modality_sloc
                               then MkProdE [] 
                               else MkProdE [VarE (sloc), VarE d] 
                if not (marker_added)
                  then do
                    end_scalars_alloc <- gensym "end_scalars_alloc"
                    return
                      (( LetE
                          (end_scalars_alloc, [], ProdTy [], Ext $ EndScalarsAllocation sloc)
                          (red_prod)
                        ), mg1, mg2)
                  else return (red_prod, mg1, mg2)
              go2 mg1 mg2 marker_added d ((rnd, (MkTy2 ty)) : rst) = do
                d' <- gensym "writecur"
                case ty of
                  _ | isPackedTy ty -> do
                    (rnd_di, freeVarToVarEnv', m1', m2') <- cursorizePackedExp mg1 mg2 False emitScalarCountBumps insideTimeit freeVarToVarEnv lenv ddfs fundefs denv tenv senv rnd
                    let rnd' = rnd_di
                    end_scalars_alloc <- gensym "end_scalars_alloc"
                    (res, m1g'', m2g'') <- case (isMutModality $ fromJust $ modality_sloc) of
                                       False -> do 
                                                 (rexpr, m1g', m2g') <- go2 mg1 mg2 True d' rst
                                                 return (LetE (d', [], (getCursorizeTyFromLocVar Nothing useMutableCursorsCall sloc_loc), projEnds rnd') rexpr, m1g', m2g')
                                       -- LetE (d', [], (getCursorizeTyFromLocVar Nothing useMutableCursorsCall sloc_loc), projEnds rnd')
                                       True -> go2 mg1 mg2 True d' rst
                    if not marker_added
                    then return (LetE (end_scalars_alloc, [], ProdTy [], Ext $ EndScalarsAllocation (sloc)) res, m1g'', m2g'')
                    else return (id res, m1g'', m2g'')

                  -- Int, Float, Sym, or Bool
                  _ | isScalarTy ty -> do
                    (rnd', freeVarToVarEnv', m1', m2') <- cursorizeExp mg1 mg2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv ddfs fundefs denv tenv senv rnd
                    let mut_loc_pts = dbgTrace (minChatLvl) "Print in DataConE: " dbgTrace (minChatLvl) (sdoc (additional_bnds, m1_dcon, m1')) dbgTrace (minChatLvl) "End in DataConE Case.\n" findMutableLocationPointingToVar d m1'
                    (additional_bnds, m1'') <- case mut_loc_pts of 
                                                      Nothing -> return ([], m1')
                                                      Just ml -> do
                                                                  void_var <- gensym "void"
                                                                  let mlName = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy ml)
                                                                  dflags <- getDynFlags
                                                                  let sizeTy = sizeOfTyD dflags ty
                                                                  let add_bnds = [(void_var, [], ProdTy [], Ext $ BumpCursorMutable mlName (LitE (fromJust sizeTy)))]
                                                                  let m1'' = updateMutableLocPtsToEnv ml m1' (d', Just ml, Nothing, S.empty) False
                                                                  return (add_bnds, m1'')
                    (res, m1g', m2g') <- go2 m1'' m2 marker_added d' rst
                    let dTy = getCursorizeTyFromLocVar Nothing useMutableCursorsCall sloc_loc
                    finalExpr <- case dTy of
                      MutCursorTy -> do
                        dCur <- gensym "writecur_cursor"
                        pure $
                          LetE (dCur, [], CursorTy, Ext $ WriteScalar (mkScalar ty) d rnd') $
                          LetE (d', [], MutCursorTy, Ext $ AddrOfCursor (VarE dCur)) $
                          mkLets additional_bnds res
                      _ ->
                        pure $
                          LetE (d', [], dTy, Ext $ WriteScalar (mkScalar ty) d rnd') $
                          mkLets additional_bnds res
                    return (finalExpr, m1g', m2g')

                  -- Write a pointer to a vector
                  VectorTy el_ty -> do
                    (rnd', freeVarToVarEnv', m1', m2') <- cursorizeExp mg1 mg2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv ddfs fundefs denv tenv senv rnd
                    (res, m1g', m2g') <- go2 m1' m2' marker_added d' rst
                    let finalExpr = LetE (d', [], getCursorizeTyFromLocVar Nothing useMutableCursorsCall sloc_loc, Ext $ WriteVector d rnd' (stripTyLocs el_ty)) res
                    return (finalExpr, m1g', m2g')

                  -- Write a pointer to a vector
                  ListTy el_ty -> do
                    (rnd', freeVarToVarEnv', m1', m2') <- cursorizeExp mg1 mg2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv ddfs fundefs denv tenv senv rnd
                    (res, m1g', m2g') <- go2 m1' m2' marker_added d' rst
                    let finalExpr = LetE (d', [], getCursorizeTyFromLocVar Nothing useMutableCursorsCall sloc_loc, Ext $ WriteList d rnd' (stripTyLocs el_ty)) res
                    return (finalExpr, m1g', m2g')

                  -- shortcut pointer
                  CursorTy -> do
                    (rnd', freeVarToVarEnv', m1', m2') <- cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv ddfs fundefs denv tenv senv rnd
                    (res, m1g', m2g') <- go2 mg1 mg2 marker_added d' rst
                    let finalExpr = LetE (d', [], CursorTy, Ext $ WriteTaggedCursor d rnd') res
                    return (finalExpr, m1g', m2g')
                  _ -> error $ "Unknown type encounterred while cursorizing DataConE. Type was " ++ show ty

          writetag <- gensym "writetag"
          after_tag <- gensym "after_tag"
          start_tag_alloc <- gensym "start_tag_alloc"
          end_tag_alloc <- gensym "end_tag_alloc"
          start_scalars_alloc <- gensym "start_scalars_alloc"
          needs_bump <- mutLocNeedsBump freeVarToVarEnv m1_dcon m2 (Just sloc_loc) (Just sloc) (L3.LitE 1)
          let (needs_bump_lts, m1') = dbgTrace (minChatLvl) "Print the bump let!!" dbgTrace (minChatLvl) (sdoc (m1_dcon, needs_bump)) dbgTrace (minChatLvl) "End printing in bump let!!" case needs_bump of 
                                        Just (b, mut_loc) -> let 
                                                    m1i = updateMutableLocPtsToEnv mut_loc m1_dcon (after_tag, Just mut_loc, Nothing, S.empty) False
                                                   in ([b], m1i)
                                        Nothing -> ([], m1_dcon)
          (after_tag_res, m1env, m2env) <- go2 m1' m2 False after_tag (zip args (lookupDataCon ddfs dcon))
          (,,,) <$> dl
            <$> mkLets additional_bnds
            <$> LetE (start_tag_alloc, [], ProdTy [], Ext $ StartTagAllocation (sloc))
            <$> LetE (writetag, [], getCursorizeTyFromLocVar Nothing useMutableCursorsCall (getDconLoc sloc_loc), Ext $ WriteTag dcon (sloc))
            <$> LetE (end_tag_alloc, [], ProdTy [], Ext $ EndTagAllocation (sloc))
            <$> LetE (start_scalars_alloc, [], ProdTy [], Ext $ StartScalarsAllocation (sloc))
            -- If any output mutable location points to the location we are doing add cursor on, then
            -- we will need to add a bump mut loc to the mutable location.
            <$> mkLets ([(after_tag, [], getCursorizeTyFromLocVar Nothing useMutableCursorsCall (getDconLoc sloc_loc), Ext $ AddCursor (sloc) (L3.LitE 1))] ++ needs_bump_lts)
            <$> return after_tag_res
            <*> return freeVarToVarEnv
            <*> return m1env
            <*> return m2env
        else do
          let sloc_loc = toLocVar slocarg
              dcon_loc = getDconLoc sloc_loc
              modality_sloc = getModality slocarg
              field_locs = getAllFieldLocsSoA sloc_loc
              selective_share_enabled = hasSelectiveShareEnabled denv
              -- sloc = case (M.lookup (fromLocVarToFreeVarsTy sloc_loc) freeVarToVarEnv) of
              --  Just v -> v
              --  Nothing -> error $ "cursorizeExp(1056): DataConE: unexpected location variable" ++ "(" ++ show sloc_loc ++ ")" ++ show freeVarToVarEnv
              --(sloc_dcon, present, freeVarToVarEnv') = case (M.lookup (fromLocVarToFreeVarsTy dcon_loc) freeVarToVarEnv) of
              --  Just v -> (v, True, freeVarToVarEnv)
              --  Nothing -> case dcon_loc of
              --    Single l -> (l, False, (M.insert (fromLocVarToFreeVarsTy dcon_loc) l freeVarToVarEnv))
              --    _ -> error $ "cursorizeExp(1059): DataConE: unexpected dcon location variable" ++ "(" ++ show (dcon, dcon_loc) ++ ")" ++ show freeVarToVarEnv
              (sloc_to_write, sloc, sloc_dcon, present, freeVarToVarEnv') = if isMutModality $ fromJust modality_sloc
                                                                           then
                                                                            let (sl_loc, sl_val_old) = case M.lookup sloc_loc m2 of 
                                                                                                      Nothing -> error "Expected to have old value for mutable location!"
                                                                                                      Just (oldv, oldl, _, _) -> case oldl of
                                                                                                                                  Nothing -> (Nothing, oldv)
                                                                                                                                  Just ol -> (Just ol, oldv)
                                                                                dcon_var = if selective_share_enabled
                                                                                           then case M.lookup dcon_loc m1 of
                                                                                                  Just ((curv, _, _, _) : _) -> curv
                                                                                                  _ -> case M.lookup dcon_loc m2 of
                                                                                                         Nothing -> error "Expected to have the data con location in the env!"
                                                                                                         Just (oldv, _, _, _) -> oldv
                                                                                           else case M.lookup dcon_loc m2 of
                                                                                                  Nothing -> error "Expected to have the data con location in the env!"
                                                                                                  Just (oldv, _, _, _) -> oldv
                                                                                (present, freeVarToVarEnv_inner) = case (M.lookup (fromLocVarToFreeVarsTy dcon_loc) freeVarToVarEnv) of 
                                                                                                                  Just v -> (True, freeVarToVarEnv)
                                                                                                                  Nothing -> case dcon_loc of 
                                                                                                                                Single l -> (False, (M.insert (fromLocVarToFreeVarsTy dcon_loc) l freeVarToVarEnv))
                                                                                                                                _ -> error $ "cursorizeExp: DataConE: unexpected dcon location variable" ++ "(" ++ show (dcon, dcon_loc) ++ ")" ++ show freeVarToVarEnv
                                                                             in (sl_loc, sl_val_old, dcon_var, present, freeVarToVarEnv_inner) 
                                                                           else
                                                                             let sloc_inner = case (M.lookup (fromLocVarToFreeVarsTy sloc_loc) freeVarToVarEnv) of
                                                                                                Just v -> v
                                                                                                Nothing -> error $ "cursorizeExp: DataConE: unexpected location variable" ++ "(" ++ show sloc_loc ++ ")" ++ show freeVarToVarEnv
                                                                                 (sloc_dcon, present, freeVarToVarEnv_inner) = case (M.lookup (fromLocVarToFreeVarsTy dcon_loc) freeVarToVarEnv) of
                                                                                                                                              Just v -> (v, True, freeVarToVarEnv)
                                                                                                                                              Nothing -> case dcon_loc of
                                                                                                                                                            Single l -> (l, False, (M.insert (fromLocVarToFreeVarsTy dcon_loc) l freeVarToVarEnv))
                                                                                                                                                            _ -> error $ "cursorizeExp: DataConE: unexpected dcon location variable" ++ "(" ++ show (dcon, dcon_loc) ++ ")" ++ show freeVarToVarEnv
                                                                              in (Just sloc_loc, sloc_inner, sloc_dcon, present, freeVarToVarEnv_inner)
              -- Return (start,end) cursors
              -- The final return value lives at the position of the out cursors:
              -- go2 :: Bool -> Var -> [(Exp2, Ty2)] -> PassM Exp3
              -- go2 marker_added d [] =
              --   if not (marker_added)
              --   then do
              --     end_scalars_alloc <- gensym "end_scalars_alloc"
              --     return (LetE (end_scalars_alloc,[],ProdTy [],Ext $ EndScalarsAllocation sloc)
              --                  (MkProdE [VarE (sloc), VarE d]))
              --   else return (MkProdE [VarE (sloc), VarE d])

              -- go2 marker_added d ((rnd, (MkTy2 ty)):rst) = do
              --   d' <- gensym "writecur"
              --   case ty of
              --     _ | isPackedTy ty -> do

              --       rnd' <- go freeVarToVarEnv tenv senv rnd
              --       end_scalars_alloc <- gensym "end_scalars_alloc"
              --       (if not marker_added
              --         then LetE (end_scalars_alloc,[],ProdTy [],Ext $ EndScalarsAllocation (sloc))
              --         else id) <$>
              --         LetE (d',[], CursorTy, projEnds rnd') <$>
              --         go2 True d' rst

              --     -- Int, Float, Sym, or Bool
              --     _ | isScalarTy ty -> do
              --       rnd' <- cursorizeExp freeVarToVarEnv ddfs fundefs denv tenv senv rnd
              --       LetE (d',[], CursorTy, Ext $ WriteScalar (mkScalar ty) d rnd') <$>
              --         go2 marker_added d' rst

              --     -- Write a pointer to a vector
              --     VectorTy el_ty -> do
              --       rnd' <- cursorizeExp freeVarToVarEnv ddfs fundefs denv tenv senv rnd
              --       LetE (d',[], CursorTy, Ext $ WriteVector d rnd' (stripTyLocs el_ty)) <$>
              --         go2 marker_added d' rst

              --     -- Write a pointer to a vector
              --     ListTy el_ty -> do
              --       rnd' <- cursorizeExp freeVarToVarEnv ddfs fundefs denv tenv senv rnd
              --       LetE (d',[], CursorTy, Ext $ WriteList d rnd' (stripTyLocs el_ty)) <$>
              --         go2 marker_added d' rst

              --     -- shortcut pointer
              --     CursorTy -> do
              --       rnd' <- cursorizeExp freeVarToVarEnv ddfs fundefs denv tenv senv rnd
              --       LetE (d',[], CursorTy, Ext $ WriteTaggedCursor d rnd') <$>
              --         go2 marker_added d' rst
              --     _ -> error $ "Unknown type encounterred while cursorizing DataConE. Type was " ++ show ty

              lookupLocVarName :: String -> M.Map FreeVarsTy Var -> LocVar -> Var
              lookupLocVarName msg env loc =
                case M.lookup (fromLocVarToFreeVarsTy loc) env of
                  Just v -> v
                  Nothing ->
                    case loc of
                      Single l -> l
                      SoA _ _ ->
                        error $
                          "cursorizePackedExp: DataConE(" ++ show dcon ++ ") : unexpected "
                            ++ msg
                            ++ " location variable "
                            ++ show loc

              lookupRegVarName :: String -> M.Map FreeVarsTy Var -> RegVar -> Var
              lookupRegVarName msg env reg =
                case M.lookup (fromRegVarToFreeVarsTy reg) env of
                  Just v -> v
                  Nothing ->
                    case reg of
                      SingleR l -> l
                      SoARv _ _ ->
                        error $
                          "cursorizePackedExp: DataConE(" ++ show dcon ++ ") : unexpected "
                            ++ msg
                            ++ " region variable "
                            ++ show reg

              lookupSelectiveShareInfo :: M.Map FreeVarsTy Var -> DataCon -> Int -> Maybe (Var, Var, Int)
              lookupSelectiveShareInfo env currDcon currIdx =
                case lookupSelectiveShareSource (L2.ShareScalarFieldBuffer currDcon currIdx) denv of
                  Nothing -> Nothing
                  Just src ->
                    case M.lookup src lenv of
                      Just (Just srcLoc@(SoA _ _)) ->
                        let srcFieldLoc =
                              case L.lookup (currDcon, currIdx) (getAllFieldLocsSoA srcLoc) of
                                Just l -> l
                                Nothing ->
                                  error $
                                    "cursorizePackedExp: DataConE(" ++ show currDcon ++ ") : missing selective-share source field "
                                      ++ show (currDcon, currIdx)
                            srcFieldVar = lookupLocVarName "selective-share source" env srcFieldLoc
                            srcFieldEndArray =
                              case M.lookup (fromRegVarToFreeVarsTy (toEndVRegVar (fromLocVarToRegVar srcLoc))) env of
                                Just v -> v
                                Nothing ->
                                  error $
                                    "cursorizePackedExp: DataConE(" ++ show currDcon ++ ") : missing selective-share source end array for "
                                      ++ show srcLoc
                            srcFieldEndIx =
                              case L.elemIndex (currDcon, currIdx) (map fst (getAllFieldLocsSoA srcLoc)) of
                                Just i -> i + 1
                                Nothing ->
                                  error $
                                    "cursorizePackedExp: DataConE(" ++ show currDcon ++ ") : missing selective-share source field index "
                                      ++ show (currDcon, currIdx)
                         in Just (srcFieldVar, srcFieldEndArray, srcFieldEndIx)
                      _ -> Nothing

              dummy :: PassM Exp3
              dummy = return $ VarE (sloc)

              go2 :: Bool -> MutableLocPtsToEnv -> MutableLocOldValueEnv -> M.Map FreeVarsTy Var -> Var -> Maybe Var -> [((DataCon, Int), LocVar)] -> [((DataCon, Int), Maybe LocVar, (Exp2, Ty2))] -> PassM (Exp3, MutableLocPtsToEnv, MutableLocOldValueEnv)
              go2 marker_added mdc1 mdc2 fvarenv aft_dloc from_rec_end aft_flocs [] = do
                let curr_soa_loc = sloc
                if not (marker_added)
                  then do
                    after_soa_loc <- gensym "aft_soa_loc"
                    res <-
                          -- Here we need to unpack the individual variables from the cursor.
                          foldlM
                            ( \res e@(_, floc) -> case floc of 
                                                 Single l -> do
                                                             -- check if location is an output mutable location!
                                                             -- we need to check the env that points to the old value of the mutable location
                                                             case M.lookup floc m2 of 
                                                                    Nothing -> do 
                                                                                let var_name = case (M.lookup (fromLocVarToFreeVarsTy $ floc) fvarenv) of
                                                                                                Just v -> v
                                                                                                Nothing -> l
                                                                                return $ res ++ [([var_name], [])] 
                                                                    Just (var_name, _, _, _) -> return $ res ++ [([var_name], [])] 
                                                 SoA _ flds -> do 
                                                               let var_name = case (M.lookup (fromLocVarToFreeVarsTy $ floc) fvarenv) of
                                                                                Just v -> v
                                                                                Nothing -> error $ "cursorizeExp (1123): DataConE: unexpected location variable" ++ "(" ++ show (dcon, floc) ++ ")" ++ show fvarenv
                                                               let (CursorArrayTy sz) = getCursorizeTyFromLocVar Nothing useMutableCursorsCall floc
                                                               -- Vidush: This indexing is actually wrong. 
                                                               -- I should make a function that given a position of a loc
                                                               -- get the exact index.
                                                               -- let (start, end, _) = getIndexPositionOfSoALocVar aft_flocs floc
                                                               (vars, bnds) <- foldlM (\(v, b) i -> do 
                                                                                        new_var <- gensym "unpack_var"
                                                                                        let bnds = [(new_var, [], CursorTy, Ext $ IndexCursorArray var_name i)]
                                                                                        return $ (v ++ [new_var], b ++ bnds)
                                                                                      
                                                                                 ) ([], []) [0..(sz - 1)]
                                                               return $ res ++ [(vars, bnds)]
                            ) [] aft_flocs
                    let after_flocs_to_vars = concatMap fst res
                    let lets_bef = concatMap snd res
                    let makeCurArr = mkMakeCursorArrayDbg after_soa_loc ([aft_dloc] ++ after_flocs_to_vars)
                    let let_mk_cur_arr = LetE (after_soa_loc, [], getCursorizeTyFromLocVar Nothing useMutableCursorsCall (SoA "" aft_flocs), makeCurArr)
                    let ret_prod = if isMutModality $ fromJust $ modality_sloc 
                                   then MkProdE []
                                   else MkProdE [VarE (curr_soa_loc), VarE (after_soa_loc)]
                    -- Vidush: A lot of code should be dead code eliminated here.
                    -- We can still create binds for them but eventually they will be dead code eliminated.
                    end_scalars_alloc <- gensym "end_scalars_alloc"
                    return
                      (( mkLets lets_bef $ let_mk_cur_arr $
                          LetE
                            (end_scalars_alloc, [], ProdTy [], Ext $ EndScalarsAllocation (curr_soa_loc))
                            (ret_prod)
                      ), mdc1, mdc2)
                  else do
                    let rec_end_var = case from_rec_end of
                          Just v -> v
                          Nothing -> error "cursorizeExp: go2: expected a recursive end."
                    let ret_prod = if isMutModality $ fromJust $ modality_sloc 
                                   then MkProdE []
                                   else MkProdE [VarE (curr_soa_loc), VarE (rec_end_var)]
                    return ((ret_prod), mdc1, mdc2)
              go2 marker_added mdc1 mdc2 fvarenv aft_dloc from_rec_end aft_flocs (((dcon, index), floc, (rnd, (MkTy2 ty))) : rst) = do
                d' <- gensym "writecur"
                case ty of
                  PackedTy _ l -> do
                    let cur_ty = getCursorizeTyFromLocVar Nothing useMutableCursorsCall l
                    (rnd', fvarenv', m1', m2') <- go insideTimeit m1 m2 fvarenv tenv senv rnd
                    end_scalars_alloc <- gensym "end_scalars_alloc"
                    res@(rest, mdc1', mdc2') <- go2 True mdc1 mdc2 fvarenv' aft_dloc (Just d') aft_flocs rst
                    res' <- case (isMutModality $ fromJust $ modality_sloc) of
                                    False -> return $ LetE (d', [], cur_ty, projEnds rnd') rest
                                    True -> return rest
                    if not marker_added
                        then return (LetE (end_scalars_alloc, [], ProdTy [], Ext $ EndScalarsAllocation (sloc)) res', mdc1', mdc2')
                        else return (id res', mdc1', mdc2')
                    
                  _ | isScalarTy ty -> do
                    -- get the location variable where the scalar must be written
                    let floc_loc = case floc of
                          Just l -> l
                          Nothing -> error $  "cursorizeExp: DataConE: expected a location for scalar buffer" ++ show (dcon, index)
                    let floc_var = lookupLocVarName "output scalar" fvarenv floc_loc
                    write_scalars_at <- gensym "write_scalars_at"
                    -- In case it exists in the mutable environment and has an old value associated with it.
                    let (floc_loc', floc_var') = case M.lookup floc_loc m2 of 
                                                        Nothing -> (Just floc_loc, floc_var)
                                                        Just (oldv, oldl, _, _) -> case oldl of
                                                                                    Nothing -> (Nothing, oldv)
                                                                                    Just ol -> (Just ol, oldv)
                    let let_assign_write_cur = LetE (write_scalars_at, [], CursorTy, (VarE floc_var'))
                    let mut_loc_pointing_at_scalar = findMutableLocationPointingToVar floc_var' mdc1
                    mdc1' <- case mut_loc_pointing_at_scalar of 
                                              Nothing -> return mdc1
                                              Just ml -> do
                                                          let mdc1i = updateMutableLocPtsToEnv ml mdc1 (write_scalars_at, Just ml, Nothing, S.singleton floc_var') True
                                                          return mdc1i 
                    let mb_share_src = lookupSelectiveShareInfo fvarenv dcon index
                    let output_field_region_start =
                          floc_loc' >>= \loc ->
                            Just $ lookupRegVarName "selective-share output start" fvarenv (fromLocVarToRegVar loc)
                    case (mb_share_src, output_field_region_start, floc_loc') of
                      (Just (share_src_cur, share_src_end_arr, share_src_end_ix), Just out_reg_start, Just _) -> do
                        let aft_flocs' =
                              map
                                ( \((d, idx'), l) ->
                                    if d == dcon && idx' == index
                                      then ((d, idx'), singleLocVar d')
                                      else ((d, idx'), l)
                                )
                                aft_flocs
                        let fvarenv'' = M.insert (fromLocVarToFreeVarsTy $ singleLocVar $ d') d' fvarenv
                        (rest, mdc1'', mdc2') <- go2 marker_added mdc1' mdc2 fvarenv'' aft_dloc from_rec_end aft_flocs' rst
                        let mut_loc_pointing_at_write_scalar = findMutableLocationPointingToVar write_scalars_at mdc1''
                        (bump_bnds, mdc1''') <- case mut_loc_pointing_at_write_scalar of 
                                                   Nothing -> return ([], mdc1'') 
                                                   Just ml -> do 
                                                               let mdc1i = updateMutableLocPtsToEnv ml mdc1'' (d', Just ml, Nothing, S.empty) False
                                                               void_var <- gensym "void"
                                                               dflags <- getDynFlags
                                                               let ml_name = getVarNameFromFreeVar fvarenv (fromLocVarToFreeVarsTy ml)
                                                               let bmp_bnd = [(void_var, [], ProdTy [], Ext $ BumpCursorMutable ml_name (LitE (fromJust $ sizeOfTyD dflags ty)))]
                                                               return (bmp_bnd, mdc1i)
                        let interm_binds = mkLets bump_bnds rest
                        ptr_delta <- gensym "share_ptr_delta"
                        should_share <- gensym "should_share"
                        share_src_end <- gensym "share_src_end"
                        share_write <- gensym "share_write"
                        let share_branch =
                              LetE
                                (share_write, [], CursorTy, Ext $ WriteCursorIndirection write_scalars_at share_src_cur share_src_end)
                                (VarE share_write)
                        return
                          ( let_assign_write_cur
                              $ LetE (share_src_end, [], CursorTy, Ext $ IndexCursorArray share_src_end_arr share_src_end_ix)
                              $ LetE (ptr_delta, [], IntTy, Ext $ SubPtr write_scalars_at out_reg_start)
                              $ LetE (should_share, [], BoolTy, PrimAppE EqIntP [VarE ptr_delta, LitE 0])
                              $ LetE
                                  ( d'
                                  , []
                                  , CursorTy
                                  , IfE
                                      (VarE should_share)
                                      share_branch
                                      (VarE write_scalars_at)
                                  )
                                  interm_binds
                          , mdc1'''
                          , mdc2'
                          )
                      _ -> do
                        (rnd', fvarenv', _m1', _m2') <- cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit fvarenv lenv ddfs fundefs denv tenv senv rnd
                        let aft_flocs' =
                              map
                                ( \((d, idx'), l) ->
                                    if d == dcon && idx' == index
                                      then ((d, idx'), singleLocVar d')
                                      else ((d, idx'), l)
                                )
                                aft_flocs
                        let fvarenv'' = M.insert (fromLocVarToFreeVarsTy $ singleLocVar $ d') d' fvarenv'
                        (rest, mdc1'', mdc2') <- go2 marker_added mdc1' mdc2 fvarenv'' aft_dloc from_rec_end aft_flocs' rst
                        let mut_loc_pointing_at_write_scalar = findMutableLocationPointingToVar write_scalars_at mdc1''
                        (bump_bnds, mdc1''') <- case mut_loc_pointing_at_write_scalar of 
                                                   Nothing -> return ([], mdc1'') 
                                                   Just ml -> do 
                                                               let mdc1i = updateMutableLocPtsToEnv ml mdc1'' (d', Just ml, Nothing, S.empty) False
                                                               void_var <- gensym "void"
                                                               dflags <- getDynFlags
                                                               let ml_name = getVarNameFromFreeVar fvarenv' (fromLocVarToFreeVarsTy ml)
                                                               let bmp_bnd = [(void_var, [], ProdTy [], Ext $ BumpCursorMutable ml_name (LitE (fromJust $ sizeOfTyD dflags ty)))]
                                                               return (bmp_bnd, mdc1i)
                        let interm_binds = mkLets bump_bnds rest
                        return (let_assign_write_cur $ LetE (d', [], CursorTy, Ext $ WriteScalar (mkScalar ty) write_scalars_at rnd') interm_binds, mdc1''', mdc2')

                  -- Write a pointer to a vector
                  VectorTy el_ty -> do
                    (rnd', fvarenv', m1', m2') <- cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit fvarenv lenv ddfs fundefs denv tenv senv rnd
                    -- get the location variable where the scalar must be written
                    let floc_loc = case floc of
                          Just l -> l
                          Nothing -> error "cursorizeExp: DataConE: expected a location for scalar buffer"
                    let floc_var = case (M.lookup (fromLocVarToFreeVarsTy $ floc_loc) fvarenv) of
                          Just v -> v
                          Nothing -> case floc_loc of
                            Single l -> l
                            SoA _ _ -> error $ "cursorizePackedExp: DataConE(" ++ show dcon ++ ") : unexpected location variable " ++ ":" ++ show floc_loc ++ "\n\n" ++ show fvarenv
                    write_vector_at <- gensym "write_vector_at"
                    let let_assign_write_cur = LetE (write_vector_at, [], CursorTy, (VarE floc_var))
                    {- Update, aft_flocs with the correct location for the scalar field -}
                    {- TODO: Audit aft_flocs'  and fvarenv'-}
                    {- TODO: Check if its fine to use singleLocVar d' here!! -}
                    let aft_flocs' =
                          map
                            ( \((d, idx'), l) ->
                                if d == dcon && idx' == index
                                  then ((d, idx'), singleLocVar d')
                                  else ((d, idx'), l)
                            )
                            aft_flocs
                    let fvarenv'' = M.insert (fromLocVarToFreeVarsTy $ singleLocVar $ d') d' fvarenv'
                    (rete, mdc1', mdc2') <- go2 marker_added mdc1 mdc2 fvarenv'' aft_dloc from_rec_end aft_flocs' rst
                    return $ (let_assign_write_cur $ LetE (d', [], CursorTy, Ext $ WriteVector write_vector_at rnd' (stripTyLocs el_ty)) rete, mdc1', mdc2')

                  -- _ -> error $ "TODO: Cursorize: cursorizePackedExp: Ty not implemented!! " ++ show (ty)

                  -- -- Write a pointer to a vector
                  -- ListTy el_ty -> do
                  --   rnd' <- cursorizeExp freeVarToVarEnv ddfs fundefs denv tenv senv rnd
                  --   LetE (d',[], CursorTy, Ext $ WriteList d rnd' (stripTyLocs el_ty)) <$>
                  --     go2 marker_added d' rst

                  -- shortcut pointer
                  -- SoA case
                  -- Fix case for indirection/shortcut pointers
                  -- TODO: Vidush, for SoA case, we should not use Cursor, but CursorArray to be precise 
                  -- and type correct, change followPtrs to do this.
                  CursorTy -> do
                    (rnd', fvarenv', m1', m2') <- cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit fvarenv lenv ddfs fundefs denv tenv senv rnd
                    after_indirection <- gensym "aft_indirection"
                    casted_var <- gensym "cast"
                    let rnd_var = case rnd' of
                          VarE v -> v
                          _ -> error "Did not expected variable!"
                    let rnd_ty = case M.lookup rnd_var tenv of 
                                              Nothing -> error "Expected type for variable!\n"
                                              Just ty -> case unTy2 ty of  
                                                        PackedTy _ l -> do
                                                                         getCursorizeTyFromLocVar'' Nothing useMutableCursorsCall l
                                                        CursorArrayTy sz -> CursorArrayTy sz
                                                        _ -> CursorTy
                    if isIndirectionTag dcon
                    then do 
                     --LetE (casted_var, [], CursorTy, Ext $ CastPtr rnd_var CursorTy) <$>
                     -- --LetE (d', [], CursorTy, Ext $ WriteTaggedCursor aft_dloc (VarE rnd_var))
                         (rete, mdc1', mdc2') <- go2 marker_added mdc1 mdc2 fvarenv' after_indirection from_rec_end aft_flocs rst
                         return $ (LetE ("_", [], ProdTy [], Ext (MemCpy aft_dloc rnd_var rnd_ty)) 
                                   $ LetE (d', [], CursorTy, Ext $ AddCursor aft_dloc (LitE (8)))  
                                   $ LetE (after_indirection, [], CursorTy, VarE d')
                                   $ rete, mdc1', mdc2')  -- Ext $ AddCursor aft_dloc (L3.LitE 8)
                    -- This is a shortcut pointer.
                    else do
                      (rete, mdc1', mdc2') <- go2 marker_added mdc1 mdc2 fvarenv' after_indirection from_rec_end aft_flocs rst
                      return $ (LetE (d', [], CursorTy, Ext $ WriteTaggedCursor aft_dloc rnd')
                                $ LetE (after_indirection, [], CursorTy, VarE d')
                                $ rete, mdc1', mdc2')  -- Ext $ AddCursor aft_dloc (L3.LitE 8)

                  -- shortcut pointer
                  -- SoA case
                  -- Fix case for indirection/shortcut pointers
                  -- TODO: Vidush, for SoA case, we should not use Cursor, but CursorArray to be precise 
                  -- and type correct, change followPtrs to do this.
                  CursorArrayTy _size -> do
                    (rnd', fvarenv', m1', m2') <- cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit fvarenv lenv ddfs fundefs denv tenv senv rnd
                    after_indirection <- gensym "aft_indirection"
                    casted_var <- gensym "cast"
                    let rnd_var = case rnd' of
                          VarE v -> v
                          _ -> error "Did not expected variable!"
                    let rnd_ty = case M.lookup rnd_var tenv of 
                                              Nothing -> error "Expected type for variable!\n"
                                              Just ty -> case unTy2 ty of  
                                                        PackedTy _ l -> do
                                                                         case l of
                                                                              Single _ -> getCursorizeTyFromLocVar Nothing useMutableCursorsCall l
                                                                              SoA _ fields -> getCursorizeTyFromLocVar Nothing useMutableCursorsCall l
                                                        CursorArrayTy sz -> CursorArrayTy sz
                                                        _ -> CursorTy
                    if isIndirectionTag dcon
                    then do 
                     --LetE (casted_var, [], CursorTy, Ext $ CastPtr rnd_var CursorTy) <$>
                     -- --LetE (d', [], CursorTy, Ext $ WriteTaggedCursor aft_dloc (VarE rnd_var))
                         (rete, mdc1', mdc2') <- go2 marker_added mdc1 mdc2 fvarenv' after_indirection from_rec_end aft_flocs rst
                         return (LetE ("_", [], ProdTy [], Ext (MemCpy aft_dloc rnd_var rnd_ty)) 
                                  $ LetE (d', [], CursorTy, Ext $ AddCursor aft_dloc (LitE (8 * _size)))  
                                -- Vidush : can get rid of after_indirection here.
                                  $ LetE (after_indirection, [], CursorTy, VarE d')
                                  $ rete, mdc1', mdc2')  -- Ext $ AddCursor aft_dloc (L3.LitE 8)
                    -- shortcut pointer
                    else do
                      -- LetE (d', [], CursorTy, Ext $ WriteTaggedCursor aft_dloc rnd')
                      --           <$> LetE (after_indirection, [], CursorTy, VarE d')
                      --           <$> go2 marker_added fvarenv' after_indirection from_rec_end aft_flocs rst -- Ext $ AddCursor aft_dloc (L3.LitE 8)
                      (rete, mdc1', mdc2') <- go2 marker_added mdc1 mdc2 fvarenv' d' from_rec_end aft_flocs rst
                      return (LetE ("_", [], ProdTy [], Ext (MemCpy aft_dloc rnd_var rnd_ty))
                              $ LetE (d', [], CursorTy, Ext $ AddCursor aft_dloc (LitE (8 * _size)))
                              $ rete, mdc1', mdc2')


                  _ -> error $ "Unknown type encounterred while cursorizing DataConE. Type was " ++ show ty

          writetag <- gensym "writetag"
          after_tag <- gensym "after_tag"
          start_tag_alloc <- gensym "start_tag_alloc"
          end_tag_alloc <- gensym "end_tag_alloc"
          start_scalars_alloc <- gensym "start_scalars_alloc"
          let exp_f_tys = zip args (lookupDataCon ddfs dcon)
          -- [((DataCon, Int), Maybe Location, (Exp2, Ty2))]
          let tyConOfDataCon = getTyOfDataCon ddfs dcon
          let allDataCons = getConOrdering ddfs tyConOfDataCon
          -- checks for abs random access nodes
          -- VS: relative offsets are turned off in the original compiler so these are also 
          -- not being handles with the SoA transformation.
          let dc' = foldr (\x dc -> if (x == dcon ++ "^") then Just x else dc) Nothing allDataCons
          let dcon' = case dc' of 
                                 Nothing -> dcon
                                 Just dc -> dc
          let numRanNodes = if (("^" `L.isSuffixOf` dcon') && (not ("^" `L.isSuffixOf` dcon)) ) then ((numRANsDataCon (M.map (fmap unTy2) ddfs) dcon)) else 0
          let locs_tys =
                map
                  ( \(idx, e) ->
                      let key = (dcon', idx + numRanNodes)
                          loc = L.lookup key field_locs
                       in (key, loc, e)
                  )
                  (zip [0 ..] exp_f_tys)
          let additional_bnds =
                if present
                  then []
                  else [(sloc_dcon, [], CursorTy, Ext $ IndexCursorArray sloc 0)]
          
          -- Vidush 
          -- Check the index logic might not be robust here.
          (additional_bnds', freeVarToVarEnv'', _) <-
            foldlM
              ( \(b, env, idx') ((_, _), loc) -> do
                  (var_for_loc, present', env', bnds) <- case (M.lookup (fromLocVarToFreeVarsTy loc) env) of
                    Just v -> return $ (v, True, env, [])
                    Nothing -> case loc of
                      Single l -> return $ (l, False, env, [])
                      SoA {} -> do
                        new_name <- gensym "field_cursor"
                        let env'' = M.insert (fromLocVarToFreeVarsTy loc) new_name env
                        return $ (new_name, False, env'', [])
                  let b' =
                        if present'
                          then b
                          else b ++ [(var_for_loc, [], getCursorizeTyFromLocVar Nothing useMutableCursorsCall sloc_loc, Ext $ IndexCursorArray sloc idx')]
                  pure (b', env', idx' + 1)
              )
              (additional_bnds, freeVarToVarEnv', 1)
              field_locs
          let footerVarForLoc floc =
                case M.lookup floc m2 of
                  Just (oldv, _, _, _) -> oldv
                  Nothing ->
                    case M.lookup (fromLocVarToFreeVarsTy floc) freeVarToVarEnv'' of
                      Just v -> v
                      Nothing ->
                        case floc of
                          Single l -> l
                          SoA _ _ ->
                            error $
                              "cursorizePackedExp: DataConE("
                                ++ show dcon
                                ++ ") : unexpected count footer location "
                                ++ show floc
          let dcon_count_footer_vars =
                if emitScalarCountBumps
                then [footerVarForLoc (getDconLoc sloc_loc)]
                else []
          let scalar_count_footer_vars =
                if emitScalarCountBumps
                then
                  Mb.mapMaybe
                    ( \(_, mb_floc, (_, MkTy2 ty)) ->
                        case mb_floc of
                          Just floc | isScalarTy ty ->
                            Just (footerVarForLoc floc)
                          _ -> Nothing
                    )
                    locs_tys
                else []
          let count_footer_vars = dcon_count_footer_vars ++ scalar_count_footer_vars
          scalar_count_bnds <-
            if null count_footer_vars
            then return []
            else do
              scalar_count_bump <- gensym "scalar_count_bump"
              return [(scalar_count_bump, [], ProdTy [], Ext $ ScalarCountBump dcon count_footer_vars)]
          (dcon_write_cur, dcon_write_prep_bnds, mut_loc_ad_bnds, m1') <-
            if selective_share_enabled
            then
              case M.lookup sloc_dcon tenv of
                Just (MkTy2 MutCursorTy) -> do
                  dcon_cur_after_bump <- gensym "dcon_cur_after_bump"
                  dcon_write_cur <- gensym "dcon_write_cur"
                  let prep_bnds =
                        [ (dcon_cur_after_bump, [], CursorTy, Ext $ DerefMutCursor sloc_dcon)
                        , (dcon_write_cur, [], CursorTy, Ext $ AddCursor dcon_cur_after_bump (LitE (-1)))
                        ]
                  let mi1 = updateMutableLocPtsToEnv dcon_loc m1 (dcon_cur_after_bump, Just dcon_loc, Nothing, S.empty) False
                  return (dcon_write_cur, prep_bnds, [], mi1)
                _ -> do
                  let mut_loc_sloc_dcon = findMutableLocationPointingToVar sloc_dcon m1
                  (mut_loc_ad_bnds, m1') <- dbgTrace (minChatLvl) "Print in SoA Dcon case: " dbgTrace (minChatLvl) (sdoc (m1, sloc_dcon)) dbgTrace (minChatLvl) "End in print dcon case SoA!!\n" case mut_loc_sloc_dcon of
                                                      Nothing -> return ([], m1)
                                                      Just ml -> do
                                                                  void <- gensym "void"
                                                                  let ml_name = getVarNameFromFreeVar freeVarToVarEnv'' (fromLocVarToFreeVarsTy ml)
                                                                  let bnd = [(void, [], ProdTy [], Ext $ BumpCursorMutable ml_name (LitE 1))]
                                                                  let mi1 = updateMutableLocPtsToEnv ml m1 (after_tag, Just ml, Nothing, S.empty) False
                                                                  return (bnd, mi1)
                  return (sloc_dcon, [], mut_loc_ad_bnds, m1')
            else do
              let mut_loc_sloc_dcon = findMutableLocationPointingToVar sloc_dcon m1
              (mut_loc_ad_bnds, m1') <- dbgTrace (minChatLvl) "Print in SoA Dcon case: " dbgTrace (minChatLvl) (sdoc (m1, sloc_dcon)) dbgTrace (minChatLvl) "End in print dcon case SoA!!\n" case mut_loc_sloc_dcon of
                                                  Nothing -> return ([], m1)
                                                  Just ml -> do
                                                              void <- gensym "void"
                                                              let ml_name = getVarNameFromFreeVar freeVarToVarEnv'' (fromLocVarToFreeVarsTy ml)
                                                              let bnd = [(void, [], ProdTy [], Ext $ BumpCursorMutable ml_name (LitE 1))]
                                                              let mi1 = updateMutableLocPtsToEnv ml m1 (after_tag, Just ml, Nothing, S.empty) False
                                                              return (bnd, mi1)
              return (sloc_dcon, [], mut_loc_ad_bnds, m1')
          (go2expr, m1'', m2') <- go2 False m1' m2 freeVarToVarEnv'' after_tag Nothing field_locs locs_tys
          let resultExpr =
                mkLets additional_bnds' $
                  LetE (start_tag_alloc, [], ProdTy [], Ext $ StartTagAllocation (sloc)) $
                    mkLets dcon_write_prep_bnds $
                      LetE (writetag, [], (getCursorizeTyFromLocVar Nothing useMutableCursorsCall (getDconLoc sloc_loc)), Ext $ WriteTag dcon (dcon_write_cur)) $
                        LetE (after_tag, [], getCursorizeTyFromLocVar Nothing useMutableCursorsCall (getDconLoc sloc_loc), Ext $ AddCursor (dcon_write_cur) (L3.LitE 1)) $
                          mkLets mut_loc_ad_bnds $
                            mkLets scalar_count_bnds $
                              LetE (end_tag_alloc, [], ProdTy [], Ext $ EndTagAllocation (sloc)) $
                                LetE (start_scalars_alloc, [], ProdTy [], Ext $ StartScalarsAllocation (sloc)) $
                                  go2expr
          return (dl resultExpr, freeVarToVarEnv'', m1'', m2')

    -- go2 :: Bool -> M.Map FreeVarsTy Var -> Var -> [((DataCon, Int), Location, (Exp2, Ty2))] -> [((DataCon, Int), Location, (Exp2, Ty2))] -> PassM Exp3
    -- go2 False after_tag (zip args (lookupDataCon ddfs dcon))

    TimeIt e t b -> do
      (Di e', freeVarToVarEnv', m1', m2') <- go True m1 m2 freeVarToVarEnv tenv senv e
      return (Di $ TimeIt e' (cursorizeTy freeVarToVarEnv' m1' m2' useMutableCursorsCall Nothing (unTy2 t)) b, freeVarToVarEnv', m1', m2')
    WithArenaE v e -> do
      (Di e', freeVarToVarEnv', m1', m2') <- go insideTimeit m1 m2 freeVarToVarEnv (M.insert v (MkTy2 ArenaTy) tenv) senv e
      return (Di $ WithArenaE v e', freeVarToVarEnv', m1', m2')
    SpawnE {} -> error "cursorizePackedExp: Unbound SpawnE"
    SyncE {} -> error "cursorizePackedExp: Unbound SyncE"
    Ext ext ->
      case ext of
        -- All locations are transformed into cursors here. Location arithmetic
        -- is expressed in terms of corresponding cursor operations.
        -- See `cursorizeLocExp`
        LetLocE locarg rhs bod -> do
          let loc = toLocVar locarg
          let modality = getModality locarg
          freeVarToVarEnv' <- do
            case loc of
              Single l ->
                if M.member (fromLocVarToFreeVarsTy loc) freeVarToVarEnv
                  then return freeVarToVarEnv
                  else return $ M.insert (fromLocVarToFreeVarsTy loc) l freeVarToVarEnv
              SoA _ _ ->
                if M.member (fromLocVarToFreeVarsTy loc) freeVarToVarEnv
                  then return $ freeVarToVarEnv
                  else do
                    name <- gensym "cursor_ptr"
                    return $ M.insert (fromLocVarToFreeVarsTy loc) name freeVarToVarEnv
          (rhs_either, m1', m2') <- dbgTrace (minChatLvl) "Print env" dbgTrace (minChatLvl) (sdoc (freeVarToVarEnv')) dbgTrace (minChatLvl) "End env cursorize\n" if (not $ isLocAlive loc bod False) 
                                                                                                                                                                  then do 
                                                                                                                                                                       (r, _, _) <- cursorizeLocExp m1 m2 useMutableCursorsCall freeVarToVarEnv' denv tenv senv locarg rhs
                                                                                                                                                                       return (r, m1, m2)
                                                                                                                                                                  else cursorizeLocExp m1 m2 useMutableCursorsCall freeVarToVarEnv' denv tenv senv locarg rhs
          let locs_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy loc)
          let (bnds, tenv', m1extended) = dbgTrace (minChatLvl) "Print envs after cursorizeLocExp: " dbgTrace (minChatLvl) (sdoc (m1', m2')) dbgTrace (minChatLvl) "End print envs after cursorizeLocExp.\n" case M.lookup (fromLocVarToFreeVarsTy loc) denv of
                Nothing -> ([], tenv, m1')
                Just vs ->
                  let vs' = map (\(v, anns, ty, e) ->
                                let e' = case (ty, e) of
                                      (CursorTy, VarE src) -> cursorValueFromMaybeTrackedMut m1' tenv src
                                      _ -> e
                                 in (v, anns, ty, e')) vs
                      extended = M.fromList [(v, MkTy2 CursorTy) | (v, _, CursorTy, _) <- vs']
                      mextended = foldr (\((v, _, _, _)) mfld -> let mutloc = findMutableLocationPointingToVar locs_var m1'
                                                                          in case mutloc of 
                                                                              Nothing -> mfld
                                                                              Just ml -> updateMutableLocPtsToEnv ml mfld (v, Just ml, Nothing, S.empty) True        
                                        ) m1' vs'                      
                   in (vs', M.union extended tenv, mextended)
          case rhs_either of
            Right (rhs', bnds', bnds_after, tenv'', senv') -> do
              let tenv''' = M.union tenv' tenv''
              let locs_var = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv') of
                    Just v -> v
                    Nothing -> case loc of
                      Single lvarrr -> lvarrr
                      SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
              let locs_ty3 :: Ty3 = if M.member loc m1 
                                    then case loc of 
                                              Single{} -> CursorTy
                                              SoA{} -> getCursorizeTyFromLocVar modality useMutableCursorsCall loc
                                    else getCursorizeTyFromLocVar modality useMutableCursorsCall loc
              let locs_ty2 = if M.member loc m1 
                             then case loc of 
                                    Single{} -> MkTy2 CursorTy 
                                    SoA{} -> getCursorizeTyFromLocVar' modality useMutableCursorsCall loc
                             else getCursorizeTyFromLocVar' modality useMutableCursorsCall loc
              case rhs of
                FromEndLE {} ->
                  if isBound locs_var tenv
                    then go insideTimeit m1extended m2' freeVarToVarEnv' (M.insert locs_var locs_ty2 tenv''') senv' bod
                    -- Discharge bindings that were waiting on 'loc'.
                    else
                       do 
                        (bod', freeVarToVarEnv'', m1'', m2'') <- go insideTimeit m1extended m2' freeVarToVarEnv' (M.insert locs_var locs_ty2 tenv') senv' bod
                        return (onDi (mkLets (bnds' ++ [(locs_var, [], locs_ty3, rhs')] ++ bnds_after ++ bnds)) bod', freeVarToVarEnv'', m1'', m2'')
                         
                -- Discharge bindings that were waiting on 'loc'.
                _ ->
                  do 
                  -- (bod', freeVarToVarEnv'', m1'', m2'') <- go insideTimeit m1extended m2' freeVarToVarEnv' (M.insert locs_var locs_ty2 tenv''') senv' bod
                  -- if loc is dead we may just want to remove it completey from the code
                  -- onDi (mkLets (bnds' ++ bnds_after ++ bnds))
                  -- || (not $ isLocAlive loc bod False)
                  if (M.member loc m1 || ((not $ isNoDeadFieldElim denv) && (not $ isLocAlive loc bod False)))
                  then do 
                       --let (vptsloc, _, _, _) = fromJust $ M.lookup loc m1
                       --let freeVarToVarEnv_update_loc = M.insert (fromLocVarToFreeVarsTy loc) vptsloc (M.delete (fromLocVarToFreeVarsTy loc) freeVarToVarEnv') 
                       (bod', freeVarToVarEnv'', m1'', m2'') <- go insideTimeit m1extended m2' freeVarToVarEnv' (M.insert locs_var locs_ty2 tenv''') senv' bod
                       dbgTrace (minChatLvl) "Print isLocAlive: " dbgTrace (minChatLvl) (sdoc (bod, loc, bnds')) dbgTrace (minChatLvl) "End isLocAlive.\n" return (bod', freeVarToVarEnv'', m1'', m2'')
                  else do 
                       (bod', freeVarToVarEnv'', m1'', m2'') <- go insideTimeit m1extended m2' freeVarToVarEnv' (M.insert locs_var locs_ty2 tenv''') senv' bod
                       return (onDi (mkLets (bnds' ++ [(locs_var, [], locs_ty3, rhs')] ++ bnds_after ++ bnds)) bod', freeVarToVarEnv'', m1'', m2'')

            Left denv' -> do
              (bod', freeVarToVarEnv'', m1'', m2'') <- cursorizePackedExp m1extended m2' useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv' lenv ddfs fundefs denv' tenv' senv bod
              return (onDi (mkLets bnds) bod', freeVarToVarEnv'', m1'', m2'') 

        {-VS: TODO: This needs to be fixed to produce the correct L3 expression. See above. -}
        {- Right now i just skip the let region, just recurse on the body-}
        LetRegE loca rhs bod -> do
          -- let loc = fromRegVarToLocVar reg_var
          -- let ty_of_loc = case loc of
          --                   SingleR _ -> CursorTy
          --                   SoARv _ flds -> CursorArrayTy (1 + length flds)
          let modality = getModality loca
          let loc = fromLocVarToRegVar (toLocVar loca)
          let ty_of_loc = getCursorizeTyFromRegVar modality useMutableCursorsCall loc
          let ty2_of_loc :: Ty2 = getCursorizeTyFromRegVar' modality useMutableCursorsCall loc
          freeVarToVarEnv' <- do
            case loc of
              SingleR l ->
                if M.member (fromRegVarToFreeVarsTy loc) freeVarToVarEnv
                  then return freeVarToVarEnv
                  else return $ M.insert (fromRegVarToFreeVarsTy loc) l freeVarToVarEnv
              SoARv _ _ -> case ((isMutModality (fromJust modality))) of 
                True -> pure freeVarToVarEnv
                False -> if ((M.member (fromRegVarToFreeVarsTy loc) freeVarToVarEnv))
                         then do
                          name <- gensym "overwrite_reg" 
                          return $ M.insert (fromRegVarToFreeVarsTy loc) name freeVarToVarEnv
                         else do
                          name <- gensym "cursor_ptr"
                          return $ M.insert (fromRegVarToFreeVarsTy loc) name freeVarToVarEnv
          (rhs_either, m1', m2') <- cursorizeRegExp m1 m2 useMutableCursorsCall freeVarToVarEnv' denv tenv senv loc rhs
          let (bnds, tenv') = case M.lookup (fromRegVarToFreeVarsTy loc) denv of
                Nothing -> ([], tenv)
                Just vs ->
                  let extended = M.fromList [(v, MkTy2 CursorTy) | (v, _, CursorTy, _) <- vs]
                   in (vs, M.union extended tenv)
          case rhs_either of
            Right (rhs', bnds', tenv'', senv') -> do
              let tenv''' = M.union tenv' tenv''
              let locs_var = case (M.lookup (fromRegVarToFreeVarsTy loc) freeVarToVarEnv') of
                    Just v -> v
                    Nothing -> case loc of
                      SingleR lvarrr -> lvarrr
                      SoARv _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
              case rhs of
                -- Discharge bindings that were waiting on 'loc'.
                _ -> do
                  case ty_of_loc of
                    MutCursorTy -> do
                      (bod', freeVarToVarEnv'', m1'', m2'') <- go insideTimeit m1' m2' freeVarToVarEnv' (M.insert locs_var (ty2_of_loc) tenv''') senv' bod 
                      return (onDi (mkLets (bnds' ++ [(locs_var, [], ty_of_loc, Ext $ AddrOfCursor rhs')] ++ bnds)) bod', freeVarToVarEnv'', m1'', m2'')
                    _ -> do
                         (bod, freeVarToVarEnv'', m1'', m2'') <- go insideTimeit m1' m2' freeVarToVarEnv' (M.insert locs_var (ty2_of_loc) tenv''') senv' bod
                         case modality of 
                               -- Vidush: TODO: Audit we can get rid of overwritten regions in case of tail call optimization
                               Just OutputMutable -> return (onDi (mkLets (bnds' ++ bnds)) bod, freeVarToVarEnv'', m1'', m2'') 
                               _ -> return (onDi (mkLets (bnds' ++ [(locs_var, [], ty_of_loc, rhs')] ++ bnds)) bod, freeVarToVarEnv'', m1'', m2'')

            Left denv' -> do 
                (bod', freeVarToVarEnv'', m1'', m2'') <- cursorizePackedExp m1' m2' useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv' lenv ddfs fundefs denv' tenv' senv bod
                return (onDi (mkLets bnds) bod', freeVarToVarEnv'', m1'', m2'')
        -- case reg_var of
        -- SingleR v -> cursorizePackedExp freeVarToVarEnv ddfs fundefs denv tenv senv bod
        -- SoARv dv _ -> cursorizePackedExp freeVarToVarEnv ddfs fundefs denv tenv senv bod

        StartOfPkdCursor cur -> return (dl $ VarE cur, freeVarToVarEnv, m1, m2)
        TagCursor a b -> do
          let a_var = case (M.lookup (fromLocVarToFreeVarsTy (toLocVar a)) freeVarToVarEnv) of
                Just v -> v
                Nothing -> case (toLocVar a) of
                  Single l -> l
                  SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
          let b_var = case (M.lookup (fromLocVarToFreeVarsTy (toLocVar b)) freeVarToVarEnv) of
                Just v -> v
                Nothing -> case (toLocVar b) of
                  Single l -> l
                  SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
          tag_cur_var <- gensym "tag_cur"
          casted_var <- gensym "cast"
          let ty3_of_field = getCursorizeTyFromLocVar Nothing useMutableCursorsCall (toLocVar a)
          let ty3_of_field2 :: Ty3 = getCursorizeTyFromLocVar'' Nothing useMutableCursorsCall (toLocVar a)
          let tag_inst = (tag_cur_var, [], ty3_of_field, Ext $ L3.TagCursor a_var b_var)
          -- Vidush: I though we got rid of all cast instructions.                          
          let cast_inst = (casted_var, [], CursorTy, Ext $ CastPtr tag_cur_var CursorTy)
          let let_bnd = mkLets $ [tag_inst] ++ [cast_inst]
          return (dl $ let_bnd (VarE casted_var), freeVarToVarEnv, m1, m2)

        -- ASSUMPTION: RetE forms are inserted at the tail position of functions,
        -- and we safely just return ends-witnesses & ends of the dilated expressions
        RetE locs v -> do
          if useMutableCursorsCall 
          then do
            (v', freeVarToVarEnv', m1', m2') <- go insideTimeit m1 m2 freeVarToVarEnv tenv senv (VarE v)
            case locs of
                 _ -> return (v', freeVarToVarEnv', m1', m2')
              -- [] -> return (v', freeVarToVarEnv')
              -- [loc] -> do
              --   let loc_to_free_var = fromLocArgToFreeVarsTy loc
              --   let locs_variable = case (M.lookup (loc_to_free_var) freeVarToVarEnv') of
              --         Just v -> v
              --         Nothing -> case (toLocVar loc) of
              --           Single lvarr -> lvarr
              --           SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"

              --   pure (mkDi (VarE (locs_variable)) [fromDi v'], freeVarToVarEnv')
              -- _ ->
              --   return $
              --     (Di $
              --       L3.MkProdE $
              --         L.foldr
              --           ( \loc acc ->
              --               let loc_to_free_var = fromLocArgToFreeVarsTy loc
              --                   locs_variable = case (M.lookup (loc_to_free_var) freeVarToVarEnv') of
              --                     Just v -> v
              --                     Nothing -> case (toLocVar loc) of
              --                       Single lvarr -> lvarr
              --                       SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
              --               in (VarE (locs_variable)) : acc
              --           )
              --           [fromDi v']
              --           locs
              --           , 
              --           freeVarToVarEnv')
          else do 
            (v', freeVarToVarEnv', m1', m2') <- go insideTimeit m1 m2 freeVarToVarEnv tenv senv (VarE v)
            case locs of
              [] -> return (v', freeVarToVarEnv', m1', m2')
              [loc] -> do
                let loc_to_free_var = fromLocArgToFreeVarsTy loc
                let locs_variable = case (M.lookup (loc_to_free_var) freeVarToVarEnv') of
                      Just v -> v
                      Nothing -> case (toLocVar loc) of
                        Single lvarr -> lvarr
                        SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"

                pure (mkDi (VarE (locs_variable)) [fromDi v'], freeVarToVarEnv', m1', m2')
              _ ->
                return $
                  (Di $
                    L3.MkProdE $
                      L.foldr
                        ( \loc acc ->
                            let loc_to_free_var = fromLocArgToFreeVarsTy loc
                                locs_variable = case (M.lookup (loc_to_free_var) freeVarToVarEnv') of
                                  Just v -> v
                                  Nothing -> case (toLocVar loc) of
                                    Single lvarr -> lvarr
                                    SoA _ _ -> error "cursorizeExp: LetLocE: unexpected location variable"
                            in (VarE (locs_variable)) : acc
                        )
                        [fromDi v']
                        locs
                        , 
                        freeVarToVarEnv', m1', m2')
        LetRegionE r sz endmut _ bod -> do
          (region_lets, freeVarToVarEnv') <- regionToBinds freeVarToVarEnv False r sz endmut
          let reg_var = regionToVar r
          let reg_ty = getCursorizeTyFromRegVar' Nothing useMutableCursorsCall reg_var
          let end_reg_ty = case endmut of
                                  L2.RegionImmutable -> MkTy2 CursorTy
                                  L2.RegionMutable -> case reg_var of
                                                           SingleR{} -> MkTy2 MutCursorTy
                                                           SoARv{} -> reg_ty

          reg_var_name <- case (M.lookup (fromRegVarToFreeVarsTy reg_var) freeVarToVarEnv') of
            Just var -> return var
            Nothing -> do
              case reg_var of
                SingleR v -> return v
                SoARv {} -> do
                  n <- gensym "region_cursor_ptr"
                  return n

          -- For end of the region
          reg_var_name_end <- case (M.lookup (fromRegVarToFreeVarsTy (toEndVRegVar reg_var)) freeVarToVarEnv') of
            Just var -> return var
            Nothing -> do
              case reg_var of
                SingleR v -> return $ toEndV v
                SoARv {} -> do
                  n <- gensym "region_cursor_ptr_end"
                  return n

          let freeVarToVarEnv'' = M.insert (fromRegVarToFreeVarsTy reg_var) reg_var_name freeVarToVarEnv'
          let freeVarToVarEnv''' = M.insert (fromRegVarToFreeVarsTy (toEndVRegVar reg_var)) reg_var_name_end freeVarToVarEnv''

          let tenv' = M.insert reg_var_name reg_ty tenv
          let tenv'' = M.insert reg_var_name_end end_reg_ty tenv'
          (bod', freeVarToVarEnv'''', m1', m2') <- go insideTimeit m1 m2 freeVarToVarEnv''' tenv'' senv bod
          return (onDi (mkLets (region_lets)) bod', freeVarToVarEnv'''', m1', m2')  
        LetParRegionE r sz _ bod -> do
          (region_lets, freeVarToVarEnv') <- regionToBinds freeVarToVarEnv True r sz L2.RegionImmutable
          (bod', freeVarToVarEnv'', m1', m2') <- go insideTimeit m1 m2 freeVarToVarEnv' tenv senv bod
          return (onDi (mkLets (region_lets)) bod', freeVarToVarEnv'', m1', m2') 
        FromEndE {} -> error $ "cursorizePackedExp: TODO " ++ sdoc ext
        BoundsCheck i bound cur -> return (dl <$> 
                                             Ext $ L3.BoundsCheck i (((unwrapLocVar . toLocVar)) bound) (((unwrapLocVar . toLocVar)) cur) Nothing Output
                                            , freeVarToVarEnv, m1, m2)
        IndirectionE tycon dcon (from, from_reg) (to, to_reg) cpy -> do
          dflags <- getDynFlags
          if gopt Opt_DisableGC dflags
            -- \|| (from_reg == "dummy" || to_reg == "dummy") -- HACK!!!
            -- [2022.03.02]: ckoparkar:WTH does this hack enable?
            then do
              let locs_var = case M.lookup (fromLocArgToFreeVarsTy to) freeVarToVarEnv of
                    Nothing -> error "Did not find variable for location!"
                    Just var -> var
              go insideTimeit m1 m2 freeVarToVarEnv tenv senv (DataConE from dcon [VarE locs_var])
            else do
              case (toLocVar from) of
                Single {} -> do
                  start <- gensym "start"
                  end <- gensym "end"
                  let from_var = case M.lookup (fromLocArgToFreeVarsTy from) freeVarToVarEnv of
                        Nothing -> error "Did not find variable for location!"
                        Just var -> var
                  let metadata_to_var = case M.lookup (fromLocArgToFreeVarsTy to) freeVarToVarEnv of
                        Nothing -> error "Did not find variable for location!"
                        Just var -> var
                  let reg_from_reg = fromLocVarToRegVar (toLocVar from_reg)
                  let metadata_to_reg = fromLocVarToRegVar (toLocVar to_reg)
                  let payload_loc = case cpy of
                        VarE payload ->
                          let old_loc = L.foldr
                                (\(loc, (oldv, _, _, _aliases)) acc ->
                                  if payload == oldv
                                  then Just loc
                                  else acc)
                                Nothing
                                (M.toList m2)
                              pts_loc = findMutableLocationPointingToVar payload m1
                              env_loc = L.foldr
                                (\(key, var) acc ->
                                  case key of
                                    FL loc | var == payload -> Just loc
                                    _ -> acc)
                                Nothing
                                (M.toList freeVarToVarEnv)
                          in case old_loc of
                            Just loc -> Just loc
                            Nothing -> case pts_loc of
                              Just loc -> Just loc
                              Nothing -> case env_loc of
                                Just loc -> Just loc
                                Nothing -> case M.lookup payload lenv >>= id of
                                  Just loc -> Just loc
                                  Nothing -> case M.lookup payload tenv of
                                    Just (MkTy2 (PackedTy _ loc)) -> Just loc
                                    _ -> Nothing
                        _ -> Nothing
                  let to_var = case payload_loc >>= (\loc -> M.lookup loc m2) of
                        Just (oldv, _, _, _) -> oldv
                        Nothing -> case payload_loc >>= (\loc -> M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv) of
                          Just var -> var
                          Nothing -> metadata_to_var
                  let payload_old_reg = payload_loc >>= (\loc -> case M.lookup loc m2 of
                        Just (_, _, Just reg, _) -> Just reg
                        _ -> Nothing)
                  let reg_to_reg = case payload_old_reg of
                        Just reg -> reg
                        Nothing -> case payload_loc of
                          Just loc -> fromLocVarToRegVar loc
                          Nothing -> metadata_to_reg
                  let from_reg_var = case M.lookup (fromRegVarToFreeVarsTy reg_from_reg) freeVarToVarEnv of
                        Nothing -> error "Did not find variable for location!"
                        Just var -> var
                  let metadata_to_reg_var = case M.lookup (fromRegVarToFreeVarsTy metadata_to_reg) freeVarToVarEnv of
                        Nothing -> error "Did not find variable for location!"
                        Just var -> var
                  let to_reg_var = case M.lookup (fromRegVarToFreeVarsTy reg_to_reg) freeVarToVarEnv of
                        Nothing -> metadata_to_reg_var
                        Just var -> var
                  -- VS : [09/20/2025 -- For SoA case, indirection with gc need a bit more thinking]
                  -- One way could be to call indirection barrier seperately on every buffer/region
                  -- Then follow them seperately for every region in the case.
                  -- For now i'm erroring out but this needs more thought.
                  (need_deref, new_vars) <- foldlM (\(ls, nvs) v -> case M.lookup v tenv of
                                                            Just (MkTy2 MutCursorTy) -> do
                                                                          new_deref <- gensym "new_deref"
                                                                          return (ls ++ [(new_deref, [], CursorTy, Ext $ DerefMutCursor v)], nvs ++ [new_deref])
                                                            _ -> return (ls, nvs ++ [v])
                                                       ) ([], []) [from_var, to_var, from_reg_var, to_reg_var]
                  return (
                    Di $
                      ( mkLets
                          (need_deref ++
                          [ ("_", [], ProdTy [], Ext (IndirectionBarrier tycon ((new_vars !! 0), (new_vars !! 2), (new_vars !! 1), (new_vars !! 3)))),
                            (start, [], CursorTy, VarE (new_vars !! 0)),
                            (end, [], CursorTy, Ext $ AddCursor (new_vars !! 0) (L3.LitE 9))
                          ])
                          (MkProdE [VarE start, VarE end])
                      ), 
                      freeVarToVarEnv, m1, m2)
                SoA dcloc flds -> do
                  -- can this be refactored into a helper function?
                  let from_loc_var = case M.lookup (fromLocArgToFreeVarsTy from) freeVarToVarEnv of 
                                          Nothing -> error "Did not find variable for location!"
                                          Just var -> var
                  let from_locs = linearizeLocVar (SoA dcloc flds) --[Single dcloc] ++ map (\(_, floc) -> floc) flds
                  let to_locs = case (toLocVar to) of
                                    Single{} -> error "Expected a SoA location!\n"
                                    SoA dc_loc flocs -> linearizeLocVar (SoA dc_loc flocs) --[Single dc_loc] ++ map (\(_, floc) -> floc) flocs
                  let to_loc_var = case M.lookup (fromLocArgToFreeVarsTy to) freeVarToVarEnv of
                        Nothing -> error "Did not find variable for location!"
                        Just var -> var
                  let reg_from_reg = fromLocVarToRegVar (toLocVar from_reg)
                  let from_reg_vars = case reg_from_reg of 
                                              SingleR{} -> error "expected an SoA region!\n"
                                              SoARv dc_reg fieldRegs -> linearizeRegVar (SoARv dc_reg fieldRegs) --[dc_reg] ++ map (\(_, floc) -> floc) fieldRegs

                  let from_reg_var = case M.lookup (fromRegVarToFreeVarsTy reg_from_reg) freeVarToVarEnv of 
                                                      Nothing -> error "Did not find region!"
                                                      Just var -> var

                  let reg_to_reg = fromLocVarToRegVar (toLocVar to_reg)
                  let to_reg_vars = case reg_to_reg of 
                                              SingleR{} -> error "expected an SoA region!\n"
                                              SoARv dc_reg fieldRegs ->  linearizeRegVar (SoARv dc_reg fieldRegs) -- [dc_reg] ++ map (\(_, floc) -> floc) fieldRegs
                  
                  let to_reg_var = case M.lookup (fromRegVarToFreeVarsTy reg_to_reg) freeVarToVarEnv of 
                                                      Nothing -> error "Did not find region!"
                                                      Just var -> var
                                              
                  let barrier_args = L.zip4 from_locs to_locs from_reg_vars to_reg_vars

                  let handle_indrs_rec = (\(lets, range, p@(flp, tp, rp, trp), b_args) r@(fl, to_loc, from_reg, to_reg) -> do
                                          case fl of 
                                            Single{} -> do
                                              start <- gensym "start"
                                              end <- gensym "end"
                                              (from_var, fvl) <- case M.lookup (fromLocVarToFreeVarsTy fl) freeVarToVarEnv of
                                                                Nothing -> case fl of 
                                                                              Single l -> return $ (l, [(l, [], CursorTy, Ext $ IndexCursorArray flp (fromJust (L.elemIndex r b_args)))])
                                                                Just var -> return $ (var, [])
                                              (to_var, tvl) <- do 
                                                               case M.lookup (fromLocVarToFreeVarsTy to_loc) freeVarToVarEnv of
                                                                Nothing -> case to_loc of 
                                                                            Single l -> return $ (l, [(l, [], CursorTy, Ext $ IndexCursorArray tp (fromJust (L.elemIndex r b_args)))])
                                                                            SoA{} -> do 
                                                                                    field_name <- gensym "field_cursor"
                                                                                    return $ (field_name, [(field_name, [], CursorTy, Ext $ IndexCursorArray tp (fromJust (L.elemIndex r b_args)))])
                                                                Just var -> return $ (var, [])

                                              (from_reg_var, frl) <- case M.lookup (fromRegVarToFreeVarsTy from_reg) freeVarToVarEnv of
                                                                          Nothing -> case from_reg of 
                                                                                          SingleR l -> return $ (l, [(l, [], CursorTy, Ext $ IndexCursorArray rp (fromJust (L.elemIndex r b_args)))])
                                                                                          SoARv{} -> do 
                                                                                                    field_name <- gensym "field_cursor"
                                                                                                    return $ (field_name, [(field_name, [], CursorTy, Ext $ IndexCursorArray rp (fromJust (L.elemIndex r b_args)))]) 
                                                                          Just var -> return $ (var, [])
                                              (to_reg_var, trl) <- case M.lookup (fromRegVarToFreeVarsTy to_reg) freeVarToVarEnv of
                                                                        Nothing -> case to_reg of 
                                                                                          SingleR l -> return $ (l, [(l, [], CursorTy, Ext $ IndexCursorArray trp (fromJust (L.elemIndex r b_args)))])
                                                                                          SoARv{} -> do
                                                                                                      field_name <- gensym "field_cursor"
                                                                                                      return $ (field_name, [(field_name, [], CursorTy, Ext $ IndexCursorArray trp (fromJust (L.elemIndex r b_args)))]) 

                                                                        Just var -> return $ (var, [])
                                              -- VS : [09/20/2025 -- For SoA case, indirection with gc need a bit more thinking]
                                              -- One way could be to call indirection barrier seperately on every buffer/region
                                              -- Then follow them seperately for every region in the case.
                                              -- For now i'm erroring out but this needs more thought.
                                              (need_deref, new_vars) <- foldlM (\(ls, nvs) v -> case M.lookup v tenv of 
                                                                                    Just (MkTy2 MutCursorTy) -> do 
                                                                                                  new_deref <- gensym "new_deref"
                                                                                                  return (ls ++ [(new_deref, [], CursorTy, Ext $ DerefMutCursor v)], nvs ++ [new_deref]) 
                                                                                    _ -> return (ls, nvs ++ [v])
                                                                               ) ([], []) [from_var, to_var, from_reg_var, to_reg_var]
                                              -- We need to make sure to get the right tycon for the the nested SoA field 
                                              -- This may be important for the GC to work properly.
                                              -- Vidush: TODO
                                              let new_let = [ ("_", [], ProdTy [], Ext (IndirectionBarrier tycon ((new_vars !! 0), (new_vars !! 2), (new_vars !! 1), (new_vars !! 3)))),
                                                              (start, [], CursorTy, VarE (from_var)),
                                                              (end, [], CursorTy, Ext $ AddCursor (from_var) (L3.LitE 9))
                                                            ]
                                              return (lets ++ fvl ++ tvl ++ frl ++ trl ++ need_deref ++ new_let, range ++ [(start, end)], p, b_args)
                                        )

                  (let_exprs, range_s, _, _) <- foldlM handle_indrs_rec ([], [], (from_loc_var, to_loc_var, from_reg_var, to_reg_var), barrier_args) barrier_args
                  start_soa <- gensym "start_soa"
                  end_soa <- gensym "end_soa"
                  let start_vars = map fst range_s
                  let end_vars = map snd range_s
                  -- TODO change cursor array ty size
                  -- TODO Fix , the size of CursorArrayTy needs to change here.
                  let let_start_soa = (start_soa, [], CursorArrayTy (L.length start_vars), mkMakeCursorArrayDbg start_soa start_vars)
                  let let_end_soa = (end_soa, [], CursorArrayTy (L.length end_vars), mkMakeCursorArrayDbg end_soa end_vars)
                  let end_prod = MkProdE [VarE start_soa, VarE end_soa]
                  let ret_let = mkLets (let_exprs ++ [let_start_soa, let_end_soa]) end_prod
                  return (Di ret_let, freeVarToVarEnv, m1, m2)
                  
        AddFixed {} -> error "cursorizePackedExp: AddFixed not handled."
        GetCilkWorkerNum -> pure (Di (Ext L3.GetCilkWorkerNum), freeVarToVarEnv, m1, m2)
        LetAvail vs bod -> do
          (bod', freeVarToVarEnv', m1', m2') <- go insideTimeit m1 m2 freeVarToVarEnv tenv senv bod
          return (onDi (Ext . L3.LetAvail vs) bod', freeVarToVarEnv', m1', m2') 
        AllocateTagHere varg tycon -> do 
          let v = toLocVar varg
          pure (dl <$> Ext $ L3.AllocateTagHere (unwrapLocVar v) tycon, freeVarToVarEnv, m1, m2)
        AllocateScalarsHere varg -> do
          let v = toLocVar varg
          pure (dl <$> Ext $ L3.AllocateScalarsHere (unwrapLocVar v), freeVarToVarEnv, m1, m2)
        SelectiveBufferShareE src tgts bod ->
          cursorizePackedExp
            m1
            m2
            useMutableCursorsCall
            emitScalarCountBumps
            insideTimeit
            freeVarToVarEnv
            lenv
            ddfs
            fundefs
            (enableSelectiveShare src tgts denv)
            tenv
            senv
            bod
        SSPush a b c d -> pure (dl <$> Ext $ L3.SSPush a (unwrapLocVar b) (unwrapLocVar c) d, freeVarToVarEnv, m1, m2)
        SSPop a b c -> pure (dl <$> Ext $ L3.SSPop a (unwrapLocVar b) (unwrapLocVar c), freeVarToVarEnv, m1, m2)
    MapE {} -> error $ "TODO: cursorizePackedExp MapE"
    FoldE {} -> error $ "TODO: cursorizePackedExp FoldE"
  where
    go intimit menv1 menv2 env = cursorizePackedExp menv1 menv2 useMutableCursorsCall emitScalarCountBumps intimit env lenv ddfs fundefs denv
    dl = Di

-- case (lv, v) of 
--                                                                                           (Just lvv, Just vv) -> case lpts of 
--                                                                                                                         Nothing -> if (vv == vpts)
--                                                                                                                                   then Just kl
--                                                                                                                                   else mred  
--                                                                                                                         Just lptsv -> if (lvv == lptsv)
--                                                                                                                                       then Just kl
--                                                                                                                                       else mred
--                                                                                           (Just lvv, Nothing) -> case lpts of 
--                                                                                                                         Nothing -> mred
--                                                                                                                         Just lptsv -> if (lvv == lptsv)
--                                                                                                                                       then Just kl
--                                                                                                                                       else mred
--                                                                                           (Nothing, Just vv) -> if (vv == vpts)
--                                                                                                                 then Just kl 
--                                                                                                                 else mred
--                                                                                           (Nothing, Nothing) -> mred 

mutLocNeedsBump :: M.Map FreeVarsTy Var -> MutableLocPtsToEnv -> MutableLocOldValueEnv -> Maybe LocVar -> Maybe Var -> (PreExp E3Ext loc (UrTy loc)) -> PassM (Maybe ((Var, [loc], (UrTy loc), (PreExp E3Ext loc (UrTy loc))), LocVar))
mutLocNeedsBump freeVarToVarEnv ptsEnv oldEnv lv v offset = do 
                                       let mutBump = L.foldr (\(kl, lst) mred -> 
                                                                        foldr (\(vpts, lpts, _endreg, _aliases) mred' -> 
                                                                                                                  case v of 
                                                                                                                      Just vv -> if (vv == vpts)
                                                                                                                                 then Just kl
                                                                                                                                 else mred'
                                                                              ) mred lst 
                                                           
                                                           ) Nothing (M.toList ptsEnv) 
                                       case mutBump of
                                               Just mutval -> do
                                                               void_val <- gensym "void"
                                                               let mutval_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy mutval)
                                                               let bind = (void_val, [], ProdTy [], Ext $ BumpCursorMutable mutval_name offset)
                                                               return $ Just (bind, mutval)
                                               Nothing -> return Nothing

cursorizeReadPackedFile ::
  MutableLocPtsToEnv -> 
  MutableLocOldValueEnv ->
  Bool ->
  Bool -> 
  Bool -> 
  M.Map FreeVarsTy Var ->
  M.Map Var (Maybe LocVar) ->
  DDefs Ty2 ->
  FunDefs2 ->
  DepEnv ->
  TyEnv Var Ty2 ->
  SyncEnv ->
  Bool ->
  Var ->
  Maybe FilePath ->
  TyCon ->
  Maybe Var ->
  Ty2 ->
  Exp2 ->
  PassM (Exp3, M.Map FreeVarsTy Var, MutableLocPtsToEnv, MutableLocOldValueEnv)
cursorizeReadPackedFile m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv isPackedContext v path tyc reg ty2 bod = do
  case reg of
    Nothing -> error $ "cursorizePackedExp: InferLocations did not set the reg for ReadPackedFile."
    Just reg_var -> do 
      (bod', freeVarToVarEnv', m1', m2') <- go insideTimeIt m1 m2 (M.insert v (MkTy2 CursorTy) tenv) bod
      return (
        mkLets
        [ (v, [], CursorTy, PrimAppE (toL3Prim $ ReadPackedFile path tyc reg ty2) []),
          (reg_var, [], CursorTy, VarE v),
          (toEndV reg_var, [], CursorTy, Ext $ AddCursor reg_var (Ext $ MMapFileSize v))
        ] bod'
        , freeVarToVarEnv', m1', m2')

  where
    go intime m1g m2g t e =
      if isPackedContext
        then 
          do 
           (e', freeVarToVarEnv', m1g', m2g') <- cursorizePackedExp m1g m2g useMutableCursorsCall emitScalarCountBumps intime freeVarToVarEnv lenv ddfs fundefs denv t senv e
           return (fromDi e', freeVarToVarEnv', m1g', m2g') 
        else cursorizeExp m1g m2g useMutableCursorsCall emitScalarCountBumps intime freeVarToVarEnv lenv ddfs fundefs denv t senv e

-- We may sometimes encounter a letloc which uses an unbound location.
--
--     letloc loc_b = loc_a + 1
--
-- i.e `loc_a` may not always be bound. If that's the case, don't process `loc_b`
-- now. Instead, add it to the dependency environment.

-- Vidush: IMPORTANT 
-- We should also keep track of exactly what bump pointer instructions we have executed for each 
-- Mutable pointer. In case any mutable pointer has been bumped, we don't want to want to bump its again.

cursorizeLocExp :: MutableLocPtsToEnv -> MutableLocOldValueEnv -> Bool -> M.Map FreeVarsTy Var -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> LocArg -> LocExp -> PassM (Either DepEnv (Exp3, [Binds Exp3], [Binds Exp3], TyEnv Var Ty2, SyncEnv), MutableLocPtsToEnv, MutableLocOldValueEnv)
cursorizeLocExp mLocPtsToEnv mLocOldValEnv useMutableCursorsCall freeVarToVarEnv denv tenv senv lvararg locExp =
  case locExp of
    AfterConstantLE i loc -> do
      let loc_var_aftc = (getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy (toLocVar loc)))
      let mut_loc_var = findMutableLocationPointingToVar loc_var_aftc mLocPtsToEnv
      let lvar = dbgTrace (minChatLvl) "Print the environments: " dbgTrace (minChatLvl) (sdoc (loc, mut_loc_var, loc_var_aftc)) dbgTrace (minChatLvl) "End in print the env in cursorizeLocExp.\n" toLocVar lvararg
      (locs_var, use_this_loc, additional_bnds, bnds_after, mLocPtsToEnv', mLocOldValEnv') <- case ((isMutModality $ fromJust $ getModality loc) || (Mb.isJust mut_loc_var && (isInputModality (getModality loc)))) of 
                                                                    -- True -> do 
                                                                    --          let loc_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy (toLocVar loc))
                                                                    --          let loc_var = toLocVar loc
                                                                    --          needs_bump <- mutLocNeedsBump freeVarToVarEnv mLocPtsToEnv mLocOldValEnv (Just loc_var) (Just loc_name) (L3.LitE i)  
                                                                    --          case needs_bump of
                                                                    --             Nothing -> if (M.member (toLocVar loc) mLocPtsToEnv)
                                                                    --                         -- The locations is already in the PtsToEnv 
                                                                    --                         -- therefore, we gets its value from the oldenv
                                                                    --                         then let old_val = dbgTrace (minChatLvl) "Print tailrecimplt in cursorizeLocExp:" dbgTrace (minChatLvl) (sdoc (mLocPtsToEnv, mLocOldValEnv, locExp)) dbgTrace (minChatLvl) "End printing tailrecimplt in cursorizeLocExp Nothing case1.\n" M.lookup (toLocVar loc) mLocOldValEnv
                                                                    --                           in case old_val of 
                                                                    --                                     Nothing -> error "Expected to have a value for the mutable location!"
                                                                    --                                     -- VS: No need to bump the mutable location in case we use the old location.
                                                                    --                                     Just (vl, Just l) -> do 
                                                                    --                                               -- let l_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy l) 
                                                                    --                                               pure (vl, l, [], [], mLocPtsToEnv, mLocOldValEnv)
                                                                    --                                     -- If the loc is not available, we just use the mut loc
                                                                    --                                     -- TODO. this may not be required / special handling?
                                                                    --                                     Just (vl, Nothing) -> do
                                                                    --                                               pure (vl, (toLocVar loc), [], [], mLocPtsToEnv, mLocOldValEnv) 
                                                                                              
                                                                    --                         else 
                                                                    --                           do
                                                                    --                         -- check if any output mutable locations point to loc. 
                                                                    --                         -- if so, we need to update the pts to for that mutable loc to lvar
                                                                    --                         -- let mLocPtsToElems = M.toList
                                                                    --                         --     mLocPtsToElems' = L.map (\(k, v) -> if l == (toLocVar loc)
                                                                    --                         --                                         then (k, lvar)
                                                                    --                         --                                         else (k, var)
                                                                    --                         --                             ) mLocPtsToElems
                                                                    --                         --   in ()
                                                                    --                         -- We need to add a dereference instruction in order to access the 
                                                                    --                         -- value of the OutputMutable location.
                                                                    --                           new_deref <- gensym "deref"
                                                                    --                           let loc_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy (toLocVar loc))
                                                                    --                           let lvar_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lvar)
                                                                    --                           let derefInst = (new_deref, [], CursorTy, Ext $ DerefMutCursor loc_name)
                                                                    --                           bump_loc_var <- gensym "void"
                                                                    --                           let bumpMutLoc = (bump_loc_var, [], ProdTy [], Ext $ BumpCursorMutable loc_name (LitE i))
                                                                    --                           -- We need to make the mutable loc point to the dereferenced value 
                                                                    --                           let mLocPtsToEnv'' = M.insert (toLocVar loc) (lvar_name, Just lvar) mLocPtsToEnv 
                                                                    --                           -- if there is no mapping of the mutable loc to its old value, we need to update it.
                                                                    --                           let mLocOldValEnv'' = if (M.member (toLocVar loc) mLocOldValEnv)
                                                                    --                                               then mLocOldValEnv
                                                                    --                                               else M.insert (toLocVar loc) (new_deref, Nothing) mLocOldValEnv
                                                                    --                           dbgTrace (minChatLvl) "Print tailrecimplt in cursorizeLocExp:" dbgTrace (minChatLvl) (sdoc (mLocPtsToEnv'', mLocOldValEnv'', locExp)) dbgTrace (minChatLvl) "End printing tailrecimplt in cursorizeLocExp Nothing case2.\n" pure (new_deref, toLocVar loc, [derefInst], [bumpMutLoc], mLocPtsToEnv'', mLocOldValEnv'')
                                                                    --             Just b -> do
                                                                    --                       -- check if any output mutable locations point to loc. 
                                                                    --                       -- if so, we need to update the pts to for that mutable loc to lvar
                                                                    --                       -- let mLocPtsToElems = M.toList
                                                                    --                       --     mLocPtsToElems' = L.map (\(k, v) -> if l == (toLocVar loc)
                                                                    --                       --                                         then (k, lvar)
                                                                    --                       --                                         else (k, var)
                                                                    --                       --                             ) mLocPtsToElems
                                                                    --                       --   in ()
                                                                    --                       -- We need to add a dereference instruction in order to access the 
                                                                    --                       -- value of the OutputMutable location.
                                                                    --                       new_deref <- gensym "deref"
                                                                    --                       let loc_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy (toLocVar loc))
                                                                    --                       let lvar_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lvar)
                                                                    --                       let derefInst = (new_deref, [], CursorTy, Ext $ DerefMutCursor loc_name)
                                                                    --                       -- bump_loc_var <- gensym "void"
                                                                    --                       -- let bumpMutLoc = (bump_loc_var, [], ProdTy [], Ext $ BumpCursorMutable loc_name (LitE i))
                                                                    --                       let bumpMutLoc = b
                                                                    --                       -- We need to make the mutable loc point to the dereferenced value 
                                                                    --                       let mLocPtsToEnv'' = M.insert (toLocVar loc) (lvar_name, Just lvar) mLocPtsToEnv 
                                                                    --                       -- if there is no mapping of the mutable loc to its old value, we need to update it.
                                                                    --                       let mLocOldValEnv'' = if (M.member (toLocVar loc) mLocOldValEnv)
                                                                    --                                           then mLocOldValEnv
                                                                    --                                           else M.insert (toLocVar loc) (new_deref, Nothing) mLocOldValEnv
                                                                    --                       dbgTrace (minChatLvl) "Print tailrecimplt in cursorizeLocExp:" dbgTrace (minChatLvl) (sdoc (mLocPtsToEnv'', mLocOldValEnv'', locExp)) dbgTrace (minChatLvl) "End printing tailrecimplt in cursorizeLocExp Just b.\n" pure (new_deref, toLocVar loc, [derefInst], [bumpMutLoc], mLocPtsToEnv'', mLocOldValEnv'')
                                                                    -- -- TODO We may need to change where output mutable locations points to.
                                                                    True -> if (M.member (toLocVar loc) mLocOldValEnv)
                                                                            then do 
                                                                              let val = M.lookup (toLocVar loc) mLocOldValEnv
                                                                              let (vl, loc_pts, _, _) = fromJust val
                                                                              needs_bump <- mutLocNeedsBump freeVarToVarEnv mLocPtsToEnv mLocOldValEnv loc_pts (Just vl) (L3.LitE i)
                                                                              case needs_bump of
                                                                                Nothing -> if (M.member (toLocVar loc) mLocPtsToEnv)
                                                                                            -- The locations is already in the PtsToEnv 
                                                                                            -- therefore, we gets its value from the oldenv
                                                                                            then let old_val = dbgTrace (minChatLvl) "Print tailrecimplt in cursorizeLocExp:" dbgTrace (minChatLvl) (sdoc (mLocPtsToEnv, mLocOldValEnv, locExp)) dbgTrace (minChatLvl) "End printing tailrecimplt in cursorizeLocExp Nothing case1.\n" M.lookup (toLocVar loc) mLocOldValEnv
                                                                                              in case old_val of 
                                                                                                        Nothing -> error "Expected to have a value for the mutable location!"
                                                                                                        -- VS: No need to bump the mutable location in case we use the old location.
                                                                                                        Just (vl, Just l, _, _) -> do 
                                                                                                                  -- let l_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy l) 
                                                                                                                  pure (vl, l, [], [], mLocPtsToEnv, mLocOldValEnv)
                                                                                                        -- If the loc is not available, we just use the mut loc
                                                                                                        -- TODO. this may not be required / special handling?
                                                                                                        Just (vl, Nothing, _, _) -> do
                                                                                                                  pure (vl, (toLocVar loc), [], [], mLocPtsToEnv, mLocOldValEnv) 
                                                                                              
                                                                                            else 
                                                                                              do
                                                                                            -- check if any output mutable locations point to loc. 
                                                                                            -- if so, we need to update the pts to for that mutable loc to lvar
                                                                                            -- let mLocPtsToElems = M.toList
                                                                                            --     mLocPtsToElems' = L.map (\(k, v) -> if l == (toLocVar loc)
                                                                                            --                                         then (k, lvar)
                                                                                            --                                         else (k, var)
                                                                                            --                             ) mLocPtsToElems
                                                                                            --   in ()
                                                                                            -- We need to add a dereference instruction in order to access the 
                                                                                            -- value of the OutputMutable location.
                                                                                              new_deref <- gensym "deref"
                                                                                              let loc_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy (toLocVar loc))
                                                                                              let lvar_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lvar)
                                                                                              let derefInst = (new_deref, [], CursorTy, Ext $ DerefMutCursor loc_name)
                                                                                              bump_loc_var <- gensym "void"
                                                                                              let bumpMutLoc = (bump_loc_var, [], ProdTy [], Ext $ BumpCursorMutable loc_name (LitE i))
                                                                                              -- We need to make the mutable loc point to the dereferenced value 
                                                                                              let mLocPtsToEnv'' = updateMutableLocPtsToEnv (toLocVar loc) mLocPtsToEnv (lvar_name, Just lvar, Just $ toEndRegVar lvararg, S.empty) False
                                                                                              -- if there is no mapping of the mutable loc to its old value, we need to update it.
                                                                                              let mLocOldValEnv'' = if (M.member (toLocVar loc) mLocOldValEnv)
                                                                                                                  then mLocOldValEnv
                                                                                                                  else M.insert (toLocVar loc) (new_deref, Nothing, Just $ toEndRegVar loc, S.empty) mLocOldValEnv
                                                                                              dbgTrace (minChatLvl) "Print tailrecimplt in cursorizeLocExp:" dbgTrace (minChatLvl) (sdoc (mLocPtsToEnv'', mLocOldValEnv'', locExp)) dbgTrace (minChatLvl) "End printing tailrecimplt in cursorizeLocExp Nothing case2.\n" pure (new_deref, toLocVar loc, [derefInst], [bumpMutLoc], mLocPtsToEnv'', mLocOldValEnv'')
                                                                                Just (b, _) -> do
                                                                                          -- check if any output mutable locations point to loc. 
                                                                                          -- if so, we need to update the pts to for that mutable loc to lvar
                                                                                          -- let mLocPtsToElems = M.toList
                                                                                          --     mLocPtsToElems' = L.map (\(k, v) -> if l == (toLocVar loc)
                                                                                          --                                         then (k, lvar)
                                                                                          --                                         else (k, var)
                                                                                          --                             ) mLocPtsToElems
                                                                                          --   in ()
                                                                                          -- We need to add a dereference instruction in order to access the 
                                                                                          -- value of the OutputMutable location.
                                                                                          --new_deref <- gensym "deref"
                                                                                          let loc_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy (toLocVar loc))
                                                                                          let lvar_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lvar)
                                                                                          --let derefInst = (new_deref, [], CursorTy, Ext $ DerefMutCursor loc_name)
                                                                                          -- bump_loc_var <- gensym "void"
                                                                                          -- let bumpMutLoc = (bump_loc_var, [], ProdTy [], Ext $ BumpCursorMutable loc_name (LitE i))
                                                                                          let bumpMutLoc = b
                                                                                          -- We need to make the mutable loc point to the dereferenced value 
                                                                                          let mLocPtsToEnv'' = updateMutableLocPtsToEnv (toLocVar loc) mLocPtsToEnv (lvar_name, Just lvar, Just $ toEndRegVar lvararg, S.empty) False 
                                                                                          -- if there is no mapping of the mutable loc to its old value, we need to update it.
                                                                                          --let mLocOldValEnv'' = if (M.member (toLocVar loc) mLocOldValEnv)
                                                                                          --                    then mLocOldValEnv
                                                                                          --                    else M.insert (toLocVar loc) (new_deref, Nothing) mLocOldValEnv
                                                                                          dbgTrace (minChatLvl) "Print tailrecimplt in cursorizeLocExp:" dbgTrace (minChatLvl) (sdoc (mLocPtsToEnv'', mLocOldValEnv, locExp)) dbgTrace (minChatLvl) "End printing tailrecimplt in cursorizeLocExp Just b.\n" pure (vl, toLocVar loc, [], [bumpMutLoc], mLocPtsToEnv'', mLocOldValEnv)
                                                                              --pure (vl, (toLocVar loc), [], [], mLocPtsToEnv, mLocOldValEnv)
                                                                            else if (Mb.isJust mut_loc_var)
                                                                            then
                                                                              do
                                                                              -- check if any output mutable locations point to loc. 
                                                                              -- if so, we need to update the pts to for that mutable loc to lvar
                                                                              -- let mLocPtsToElems = M.toList
                                                                              --     mLocPtsToElems' = L.map (\(k, v) -> if l == (toLocVar loc)
                                                                              --                                         then (k, lvar)
                                                                              --                                         else (k, var)
                                                                              --                             ) mLocPtsToElems
                                                                              --   in ()
                                                                              -- We need to add a dereference instruction in order to access the 
                                                                              -- value of the OutputMutable location.
                                                                                --new_deref <- gensym "deref_ij"
                                                                                let loc_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy (toLocVar loc))
                                                                                let lvar_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lvar)
                                                                                --let derefInst = (new_deref, [], CursorTy, Ext $ DerefMutCursor loc_name)
                                                                                let mut_loc = fromJust $ mut_loc_var 
                                                                                let mut_loc_varname = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy mut_loc)
                                                                                bump_loc_var <- gensym "void_ij"
                                                                                let bumpMutLoc = (bump_loc_var, [], ProdTy [], Ext $ BumpCursorMutable (mut_loc_varname) (LitE i))
                                                                                -- We need to make the mutable loc point to the dereferenced value 
                                                                                let mLocPtsToEnv'' = updateMutableLocPtsToEnv mut_loc mLocPtsToEnv (lvar_name, Just mut_loc, Nothing, S.empty) False
                                                                                -- if there is no mapping of the mutable loc to its old value, we need to update it.
                                                                                (mLocOldValEnv'', nbmoldenv) <- do 
                                                                                                    if (M.member mut_loc mLocOldValEnv)
                                                                                                    then return (mLocOldValEnv, [])
                                                                                                    else updateMutableLocOldValueEnv mut_loc mLocOldValEnv (lvar_name, Nothing, Nothing, S.empty) False
                                                                                pure (loc_name, toLocVar loc, nbmoldenv, [bumpMutLoc], mLocPtsToEnv'', mLocOldValEnv'')
                                                                            else
                                                                              do
                                                                              -- check if any output mutable locations point to loc. 
                                                                              -- if so, we need to update the pts to for that mutable loc to lvar
                                                                              -- let mLocPtsToElems = M.toList
                                                                              --     mLocPtsToElems' = L.map (\(k, v) -> if l == (toLocVar loc)
                                                                              --                                         then (k, lvar)
                                                                              --                                         else (k, var)
                                                                              --                             ) mLocPtsToElems
                                                                              --   in ()
                                                                              -- We need to add a dereference instruction in order to access the 
                                                                              -- value of the OutputMutable location.
                                                                                new_deref <- gensym "deref"
                                                                                let loc_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy (toLocVar loc))
                                                                                let lvar_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lvar)
                                                                                let derefInst = (new_deref, [], CursorTy, Ext $ DerefMutCursor loc_name)
                                                                                bump_loc_var <- gensym "void"
                                                                                let bumpMutLoc = (bump_loc_var, [], ProdTy [], Ext $ BumpCursorMutable loc_name (LitE i))
                                                                                -- We need to make the mutable loc point to the dereferenced value 
                                                                                let mLocPtsToEnv'' = updateMutableLocPtsToEnv (toLocVar loc) mLocPtsToEnv (lvar_name, Just lvar, Just $ toEndRegVar lvararg, S.empty) False
                                                                                -- if there is no mapping of the mutable loc to its old value, we need to update it.
                                                                                let mLocOldValEnv'' = if (M.member (toLocVar loc) mLocOldValEnv)
                                                                                                      then mLocOldValEnv
                                                                                                      else M.insert (toLocVar loc) (new_deref, Nothing, Just $ toEndRegVar loc, S.empty) mLocOldValEnv
                                                                                pure (new_deref, toLocVar loc, [derefInst], [bumpMutLoc], mLocPtsToEnv'', mLocOldValEnv'')
                                                                    _ -> do
                                                                          let lvar_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lvar)
                                                                          let loc_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy (toLocVar loc))
                                                                          (new_key_vals, after_bnds) <- foldlM (\(kvals, bnds) (key, lst) -> 
                                                                                                                      foldlM (\(kvals', bnds') (vval, lval, endreg, aliases) ->
                                                                                                                                            case lval of 
                                                                                                                                                  Nothing -> if vval == loc_name
                                                                                                                                                             then
                                                                                                                                                              do
                                                                                                                                                              let key_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy key) 
                                                                                                                                                              bump_loc_var <- gensym "void"    
                                                                                                                                                              let aft_bnd = (bump_loc_var, [], ProdTy [], Ext $ BumpCursorMutable key_name (LitE i)) 
                                                                                                                                                              return (kvals' ++ [(key, (lst ++ [(lvar_name, Just lvar, Just $ toEndRegVar lvararg, aliases)]))], bnds' ++ [aft_bnd])
                                                                                                                                                             else return $ (kvals' ++ [(key, (lst ++ [(vval, lval, endreg, aliases)]))], bnds')
                                                                                                                                                  Just l -> if l == (toLocVar loc)
                                                                                                                                                            then
                                                                                                                                                              do
                                                                                                                                                              let key_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy key)
                                                                                                                                                              bump_loc_var <- gensym "void"
                                                                                                                                                              let aft_bnd = (bump_loc_var, [], ProdTy [], Ext $ BumpCursorMutable key_name (LitE i)) 
                                                                                                                                                              return (kvals' ++ [(key, (lst ++ [(lvar_name, Just lvar, Just $ toEndRegVar lvararg, aliases)]))], bnds' ++ [aft_bnd])
                                                                                                                                                            else do 
                                                                                                                                                              return $ (kvals' ++ [(key, (lst ++ [(vval, lval, endreg, aliases)]))], bnds')
                                                                                                                          ) (kvals, bnds) lst
                                                                                                                                ) ([], []) (M.toList mLocPtsToEnv)
                                                                          let mLocPtsToEnv'' = dbgTrace (minChatLvl) "Print tailrecimplt in cursorizeLocExp:" dbgTrace (minChatLvl) (sdoc (new_key_vals, after_bnds, locExp, mLocPtsToEnv, mLocOldValEnv)) dbgTrace (minChatLvl) "End printing tailrecimplt in cursorizeLocExp False.\n" M.fromList new_key_vals
                                                                          let loc_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy (toLocVar loc))
                                                                          pure (loc_name, toLocVar loc, [], after_bnds, mLocPtsToEnv'', mLocOldValEnv) 
      -- let locs_var = case (M.lookup ((fromLocVarToFreeVarsTy . toLocVar) loc) freeVarToVarEnv) of
      --       Just v -> v
      --       Nothing -> error $ "cursorizeLocExp: AfterConstantLE: unexpected location variable: " ++ "(" ++ show locExp ++ "\n,\n" ++ (show (toLocVar loc, lvar)) ++ "\n)\n" ++ show freeVarToVarEnv
      let loc_ty = M.lookup locs_var tenv
          rhs = dbgTrace (minChatLvl) "Print in cursorizeLocExp: " dbgTrace (minChatLvl) (sdoc (lvar, loc, locs_var, loc_ty, locExp, mLocPtsToEnv', mLocOldValEnv')) dbgTrace (minChatLvl) "End in cursorizeLocExp\n." Ext $ AddCursor locs_var (LitE i)
          lvar_to_name = case (M.lookup (fromLocVarToFreeVarsTy lvar) freeVarToVarEnv) of
                            Just v -> v
                            Nothing -> error $ "cursorizeLocExp: AfterConstantLE: unexpected location variable: " ++ "(" ++ show locExp ++ "," ++ (show lvar) ++ ")" ++ show freeVarToVarEnv
          in if isBound (getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy (toLocVar loc))) tenv
             then pure $ (Right (rhs, additional_bnds, bnds_after, tenv, senv), mLocPtsToEnv', mLocOldValEnv')
             else pure $ (Left $ M.insertWith (++) ((fromLocVarToFreeVarsTy . toLocVar) loc) (additional_bnds ++ [(lvar_to_name, [], CursorTy, rhs)]) denv, mLocPtsToEnv', mLocOldValEnv')
    -- TODO: handle product types here

    {- [2018.03.07]:

    Changing it's meaning to just be "after a variable", but not offset from any
    particular location. Such an offset requires calculating the size of the variable.
    For BigInfinite regions, this is simple:

        size = (endof v) - v

    But Infinite regions do not support sizes yet. Re-enable this later.
    -}
    AfterVariableLE v locarg was_stolen -> do
      let lvar = toLocVar lvararg
          lvar_name = case (M.lookup (fromLocVarToFreeVarsTy lvar) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show locExp ++ "," ++ (show (lvar)) ++ ")" ++ show freeVarToVarEnv
      let vty = case M.lookup v tenv of
            Just ty -> ty
            Nothing -> case M.lookup v senv of
              Just pending_bnds ->
                let tenv' = foldr (\(v1, _, _, ty2, _) env -> M.insert v1 ty2 env) tenv pending_bnds
                 in case M.lookup v tenv' of
                      Nothing -> error ("cursorizeLocExp: AfterVariableLE, undound var: " ++ sdoc v)
                      Just ty -> ty
              Nothing -> error $ "cursorizeLocExp: Var " ++ sdoc v ++ " not found. "
          loc = toLocVar locarg
          locs_var = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error "cursorizeLocExp: AfterConstantLE: unexpected location variable"
          -- find mutable location pointing to loc
          mut_loc_pointing_to_loc = findMutableLocationPointingToVar (toEndV v) mLocPtsToEnv
          mLocPtsToEnv' = case mut_loc_pointing_to_loc of 
                                      Nothing -> mLocPtsToEnv
                                      Just l -> let m1 = updateMutableLocPtsToEnv l mLocPtsToEnv (lvar_name, Just lvar, Nothing, S.empty) False
                                                 in m1
          bod = dbgTrace (minChatLvl) "Print in cursorizeLocExp AfterVariableLE: " dbgTrace (minChatLvl) (sdoc (lvar, mut_loc_pointing_to_loc, locs_var, v)) dbgTrace (minChatLvl) "End in cursorizelocexp AfterVariableLE.\n"  case unTy2 vty of
            PackedTy {} -> VarE (toEndV v)
            CursorTy -> VarE (toEndV v)
            {-
                              IntTy -> let sizeVal = LitE (fromJust $ sizeOfTy IntTy)
                                           rhs = Ext $ AddCursor loc sizeVal
                                       in rhs
                              FloatTy -> let sizeVal = LitE (fromJust $ sizeOfTy FloatTy)
                                             rhs = Ext $ AddCursor loc sizeVal
                                         in rhs
                              BoolTy -> let sizeVal = LitE (fromJust $ sizeOfTy BoolTy)
                                            rhs = Ext $ AddCursor loc sizeVal
                                        in rhs
                              CharTy -> let sizeVal = LitE (fromJust $ sizeOfTy CharTy)
                                            rhs = Ext $ AddCursor loc sizeVal
                                        in rhs
                              SymTy -> let sizeVal = LitE (fromJust $ sizeOfTy SymTy)
                                           rhs = Ext $ AddCursor loc sizeVal
                                       in rhs
                              VectorTy elty -> let sizeVal = LitE (fromJust $ sizeOfTy (VectorTy elty))
                                                   rhs = Ext $ AddCursor loc sizeVal
                                               in rhs
                              ListTy elty -> let sizeVal = LitE (fromJust $ sizeOfTy (ListTy elty))
                                                 rhs = Ext $ AddCursor loc sizeVal
                                             in rhs
            -}
            oth -> error $ "cursorizeLocExp: AfterVariable TODO " ++ sdoc oth
      if isBound locs_var tenv
        then
          if was_stolen
            then pure $ (Right (bod, [], [], tenv, senv), mLocPtsToEnv', mLocOldValEnv)
            -- The continuation was not stolen. It's safe to discharge all
            -- pending bindings of this particular variable.
            else do
              case M.lookup v senv of
                Nothing -> pure $ (Right (bod, [], [], tenv, senv), mLocPtsToEnv', mLocOldValEnv)
                Just pending_bnds -> do
                  let tenv' = foldr (\(v1, _, _, ty2, _) env -> M.insert v1 ty2 env) tenv pending_bnds
                      bnds = map (\(a, b, c, ty2, e) ->
                              let e' = case (c, ty2, e) of
                                         (CursorTy, MkTy2 MutCursorTy, VarE src) -> Ext $ DerefMutCursor src
                                         (CursorTy, _, VarE src) -> cursorValueFromMaybeTrackedMut mLocPtsToEnv' tenv src
                                         _ -> e
                               in (a, b, c, e')) pending_bnds
                  pure $ (Right (bod, bnds, [], tenv', M.delete v senv),  mLocPtsToEnv', mLocOldValEnv)
        else pure $ (Left $ M.insertWith (++) (fromLocVarToFreeVarsTy loc) [(lvar_name, [], CursorTy, bod)] denv,  mLocPtsToEnv, mLocOldValEnv)
    FromEndLE locarg -> do
      let loc = toLocVar locarg
          lvar = toLocVar lvararg
          locs_var = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error $ "cursorizeLocExp: FromEndLE: unexpected location variable" ++ "(" ++ show locExp ++ ", Location: " ++ (show (loc)) ++ ")" ++ show freeVarToVarEnv
          lvar_name = case (M.lookup (fromLocVarToFreeVarsTy lvar) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show locExp ++ "," ++ (show (lvar)) ++ ")" ++ show freeVarToVarEnv
          mut_loc_pointing_to_loc = findMutableLocationPointingToVar locs_var mLocPtsToEnv
          fromEndRhs = cursorValueFromMaybeTrackedMut mLocPtsToEnv tenv locs_var
      mLocPtsToEnv' <- case mut_loc_pointing_to_loc of 
                                    Nothing -> return mLocPtsToEnv
                                    Just mloc -> do 
                                                  let m1' = updateMutableLocPtsToEnv mloc mLocPtsToEnv (lvar_name, Just mloc, Nothing, S.singleton locs_var) False
                                                  return m1'
      if isBound locs_var tenv
      then dbgTrace (minChatLvl) "Print in cursorizeLocExp FromEndLE: " dbgTrace (minChatLvl) (sdoc (lvar, lvar_name, loc,locs_var, mLocPtsToEnv')) dbgTrace (minChatLvl) "End printing in cursorizeLocExp FromEndE Right case.\n" pure $ (Right (fromEndRhs, [], [], tenv, senv),  mLocPtsToEnv', mLocOldValEnv)
      else dbgTrace (minChatLvl) "Print in cursorizeLocExp FromEndLE: " dbgTrace (minChatLvl) (sdoc (lvar, lvar_name, loc, locs_var, mLocPtsToEnv')) dbgTrace (minChatLvl) "End printing in cursorizeLocExp FromEndE Left case.\n" pure $ (Left $ M.insertWith (++) (fromLocVarToFreeVarsTy loc) [(lvar_name, [], CursorTy, fromEndRhs)] denv,  mLocPtsToEnv', mLocOldValEnv)
    StartOfRegionLE r -> case r of
      GlobR v _ -> do
                    let lvar = toLocVar lvararg
                    let lvarname = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lvar)
                    case (getModality lvararg) of 
                            Just OutputMutable -> do
                                            let mLocPtsToEnv' = updateMutableLocPtsToEnv lvar mLocPtsToEnv (v, Nothing, Just $ toEndVRegVar (regionToVar r), S.empty) False
                                            let mLocOldValEnv' = M.insert lvar (v, Nothing, Just $ toEndVRegVar (regionToVar r), S.empty) mLocOldValEnv
                                            -- Vidush: in case its outputmutable we just need to take the address of the cursor
                                            pure $ (Right (Ext $ AddrOfCursor (VarE v), [], [], tenv, senv),  mLocPtsToEnv', mLocOldValEnv')
                            _ -> pure $ (Right (VarE v, [], [], tenv, senv),  mLocPtsToEnv, mLocOldValEnv)
      VarR v -> pure $ (Right (VarE v, [], [], tenv, senv),  mLocPtsToEnv, mLocOldValEnv)
      DynR v _ -> pure $ (Right (VarE v, [], [], tenv, senv),  mLocPtsToEnv, mLocOldValEnv)
      -- TODO: docs
      MMapR _v -> pure $ (Left denv,  mLocPtsToEnv, mLocOldValEnv)
      {- VS: TODO: This needs to be fixed. There should be an env. for tracking complex regions liks SoA regs-}
      SoAR dr fregs -> do
        let lvar = toLocVar lvararg
        let lvarty = getCursorizeTyFromLocVar'' Nothing useMutableCursorsCall lvar
        let lvarname = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lvar)
        let regions_var = case (M.lookup (fromRegVarToFreeVarsTy (regionToVar r)) freeVarToVarEnv) of
              Just v -> v
              Nothing -> error "cursorizeLocExp: StartOfRegionLE: unexpected location variable"
        case (getModality lvararg) of
                Just OutputMutable -> do
                                let mLocPtsToEnv' = updateMutableLocPtsToEnv lvar mLocPtsToEnv (regions_var, Nothing, Just $ toEndVRegVar (regionToVar r), S.empty) False 
                                let mLocOldValEnv' = M.insert lvar (regions_var, Nothing, Just $ toEndVRegVar (regionToVar r), S.empty) mLocOldValEnv
                                pure (Right (Ext $ InitCursor lvarty, [], [("_", [], ProdTy [], Ext $ MemCpy lvarname regions_var lvarty)], tenv, senv), mLocPtsToEnv', mLocOldValEnv')
                _ -> pure $ (Right (VarE (regions_var), [], [], tenv, senv), mLocPtsToEnv, mLocOldValEnv)
    FreeLE -> pure $ (Left denv,  mLocPtsToEnv, mLocOldValEnv) -- AUDIT: should we just throw away this information?
    InRegionLE {} -> error $ "cursorizeExp: TODO InRegionLE"
    GetDataConLocSoA loc -> do
      -- Read only operataion on a SoA location!
      -- For an SoA location we make it point to itself for now
      let loc_from_logarg = toLocVar loc
          sourceModality = getModality loc
          targetModality = getModality lvararg
          loc_region = toRegVar loc
          lvar = toLocVar lvararg
          targetLocTy = getCursorizeTyFromLocVar'' targetModality useMutableCursorsCall lvar
          loc_var = dbgTrace (minChatLvl) "Print in cursorizeLocExp GetDataConLocSoA: " dbgTrace (minChatLvl) (sdoc (mLocPtsToEnv, lvar)) dbgTrace (minChatLvl) "End in GetDataConLocSoA.\n" case (M.lookup (fromLocVarToFreeVarsTy loc_from_logarg) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error "cursorizeLocExp: GetDataConLocSoA: unexpected location variable"
          lvar_name = case (M.lookup (fromLocVarToFreeVarsTy lvar) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show locExp ++ "," ++ (show (lvar)) ++ ")" ++ show freeVarToVarEnv
      -- Read only so just make it point to itself.
      (mLocPtsToEnv', mLocOldValEnv', rhs, additional_bnds) <-
        let rhs_tmp =
              if isMutModality' targetModality
                then Ext $ AddrOfCursor $ Ext $ IndexCursorArray loc_var 0
                else Ext $ IndexCursorArray loc_var 0
         in case isMutModality' sourceModality of
              True -> do
                if not (M.member loc_from_logarg mLocOldValEnv)
                  then do
                    cpy <- gensym "cpy"
                    let cpy_ty = getCursorizeTyFromLocVar'' sourceModality useMutableCursorsCall loc_from_logarg
                    let memcpy_intr = [(cpy, [], cpy_ty, Ext $ InitCursor cpy_ty), ("_", [], ProdTy [], Ext $ MemCpy cpy loc_var cpy_ty)]
                    let mLocPtsToEnv_i = updateMutableLocPtsToEnv loc_from_logarg mLocPtsToEnv (cpy, Nothing, Just loc_region, S.empty) False
                    let mLocOldValEnv_i = M.insert loc_from_logarg (cpy, Nothing, Just loc_region, S.empty) mLocOldValEnv
                    pure (mLocPtsToEnv_i, mLocOldValEnv_i, rhs_tmp, memcpy_intr)
                  else pure (mLocPtsToEnv, mLocOldValEnv, rhs_tmp, [])
              _ -> pure (mLocPtsToEnv, mLocOldValEnv, rhs_tmp, [])
      if isBound loc_var tenv
            then pure $ (Right (rhs, additional_bnds, [], tenv, senv),  mLocPtsToEnv', mLocOldValEnv')
            -- CursorArrayTy (1 + length (getAllFieldLocsSoA loc_from_logarg))
            else pure $ (Left $ M.insertWith (++) (fromLocVarToFreeVarsTy loc_from_logarg) (additional_bnds ++ [(lvar_name, [], targetLocTy, rhs)]) denv,  mLocPtsToEnv', mLocOldValEnv')
    GetFieldLocSoA i loc -> do
      {- VS: TODO: don't use unwrap loc var and keep an env mapping loc to its variable name in the program -}
      let loc_from_locarg = toLocVar loc
          lvar = toLocVar lvararg
          sourceModality = getModality loc
          targetModality = getModality lvararg
          loc_region = toRegVar loc
          field_locs = getAllFieldLocsSoA loc_from_locarg
          targetLocTy = getCursorizeTyFromLocVar'' targetModality useMutableCursorsCall lvar
          loc_var = case (M.lookup (fromLocVarToFreeVarsTy loc_from_locarg) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error "cursorizeLocExp: GetDataConLocSoA: unexpected location variable"
          field_loc = case L.lookup i field_locs of
            Just loc -> loc
            Nothing -> error "cursorizeLocExp: GetFieldLocSoA: field location not found!"
          field_loc_elem = (i, field_loc)
          elem_idx = case (L.elemIndex field_loc_elem field_locs) of
            Just idx -> idx
            Nothing -> error "cursorizeLocExp: GetFieldLocSoA: field location not found!"
          lvar_name = dbgTrace (minChatLvl) "Print in GetFieldLocSoA: " dbgTrace (minChatLvl) (sdoc (mLocPtsToEnv, loc, sourceModality, targetModality, lvar)) dbgTrace (minChatLvl) "End in GetFieldLocSoA.\n" case (M.lookup (fromLocVarToFreeVarsTy lvar) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show locExp ++ "," ++ (show (lvar)) ++ ")" ++ show freeVarToVarEnv
      -- () <- case modality of 
      --                                           Just OutputMutable -> pure (M.insert loc_from_locarg (loc_var, Nothing, Just loc_region) mLocPtsToEnv, M.insert loc_from_locarg (loc_var, Nothing, Just loc_region) mLocOldValEnv) 
      --                                           _ -> pure (mLocPtsToEnv, mLocOldValEnv)
      (mLocPtsToEnv', mLocOldValEnv', rhs, additional_lets, lets_before) <- case (isMutModality' targetModality && not (M.member lvar mLocPtsToEnv)) of 
                                                                      True -> do 
                                                                                --m1 = M.insert loc_from_locarg (loc_var, Nothing, Just loc_region, S.empty) mLocPtsToEnv
                                                                                --m2 = M.insert loc_from_locarg (loc_var, Nothing, Just loc_region, S.empty) mLocOldValEnv
                                                                                --m1 = M.insert lvar (lvar_name, Just lvar, Just loc_region, S.empty) mLocPtsToEnv
                                                                                let m1 = updateMutableLocPtsToEnv lvar mLocPtsToEnv (lvar_name, Just lvar, Just loc_region, S.empty) False
                                                                                (m2, deref_bnds) <- updateMutableLocOldValueEnv lvar mLocOldValEnv (lvar_name, Just lvar, Just loc_region, S.empty) False
                                                                                (m1', m2', deref_bnds') <- case isMutModality' sourceModality of
                                                                                  True -> do
                                                                                    let m1i = updateMutableLocPtsToEnv loc_from_locarg m1 (loc_var, Just lvar, Just loc_region, S.empty) True
                                                                                    (m2i, deref_bnds_i) <- updateMutableLocOldValueEnv loc_from_locarg m2 (loc_var, Just lvar, Just loc_region, S.empty) True
                                                                                    pure (m1i, m2i, deref_bnds_i)
                                                                                  _ -> pure (m1, m2, [])
                                                                                case field_loc of 
                                                                                  Single{} -> do
                                                                                            let (start, end, _) = getIndexPositionOfSoALocVar useMutableCursorsCall Nothing field_locs field_loc 
                                                                                            return $ (m1', m2', Ext $ AddrOfCursor $ Ext $ IndexCursorArray loc_var start, [], deref_bnds ++ deref_bnds')
                                                                                  SoA _ fregs -> do
                                                                                            let CursorArrayTy sz = getCursorizeTyFromLocVar Nothing useMutableCursorsCall field_loc
                                                                                            let (start, end, _) = getIndexPositionOfSoALocVar useMutableCursorsCall Nothing field_locs field_loc
                                                                                            --let start = L.elemIndex (i, field_loc) field_locs
                                                                                            --let start_val = fromJustDef (-1) start
                                                                                            res <- foldlM (\bnds i -> do 
                                                                                                                      new_var <- gensym "unpack_loc"
                                                                                                                      return $ bnds ++ [ (new_var, (new_var, [], CursorTy, Ext $ IndexCursorArray loc_var i)) ]
                                                                                                          ) [] [(start)..(end - 1)]
                                                                                            let vars = map fst res
                                                                                            let bnds = map snd res
                                                                                            return $ (m1', m2', mkMakeCursorArrayDbg lvar_name vars, bnds, deref_bnds ++ deref_bnds')
                                                                      False -> case field_loc of 
                                                                                  Single{} -> do
                                                                                            let (start, end, _) = getIndexPositionOfSoALocVar useMutableCursorsCall Nothing field_locs field_loc 
                                                                                            return $ (mLocPtsToEnv, mLocOldValEnv, Ext $ IndexCursorArray loc_var start, [], [])
                                                                                  SoA _ fregs -> do
                                                                                            let CursorArrayTy sz = getCursorizeTyFromLocVar Nothing useMutableCursorsCall field_loc
                                                                                            let (start, end, _) = getIndexPositionOfSoALocVar useMutableCursorsCall Nothing field_locs field_loc
                                                                                            --let start = L.elemIndex (i, field_loc) field_locs
                                                                                            --let start_val = fromJustDef (-1) start
                                                                                            res <- foldlM (\bnds i -> do 
                                                                                                                      new_var <- gensym "unpack_loc"
                                                                                                                      return $ bnds ++ [ (new_var, (new_var, [], CursorTy, Ext $ IndexCursorArray loc_var i)) ]
                                                                                                          ) [] [(start)..(end - 1)]
                                                                                            let vars = map fst res
                                                                                            let bnds = map snd res
                                                                                            return $ (mLocPtsToEnv, mLocOldValEnv, mkMakeCursorArrayDbg lvar_name vars, bnds, [])
      if isBound loc_var tenv
            then pure $ (Right (rhs, additional_lets, lets_before, tenv, senv),  mLocPtsToEnv', mLocOldValEnv')
            else pure $ (Left $ M.insertWith (++) (fromLocVarToFreeVarsTy loc_from_locarg) (additional_lets ++ [(lvar_name, [], targetLocTy, rhs)]) denv,  mLocPtsToEnv', mLocOldValEnv')
    GenSoALoc dloc flocs -> do
            {- VS: TODO: don't use unwrap loc var and keep an env mapping loc to its variable name in the program -}
            let dcloc_var = case (M.lookup (fromLocVarToFreeVarsTy (toLocVar dloc)) freeVarToVarEnv) of
                              Just v -> v
                              Nothing -> error "cursorizeLocExp: GenSoALoc: unexpected data constructor location variable"
            res <-
                  mapM
                    (\(_, loc) -> let modality_floc = getModality loc
                                      locfromlocarg = toLocVar loc
                                   in case (toLocVar loc) of 
                                        -- Vidush
                                        -- We need to see if this is an output mutable location
                                        Single{} -> case modality_floc of 
                                                            Just OutputMutable -> case M.lookup locfromlocarg mLocOldValEnv of 
                                                                                                Nothing -> error "Expected to have location in env!"
                                                                                                Just (var, _, _, _) -> pure $ [(var, [])]
                                                            Just InputMutable -> case M.lookup locfromlocarg mLocPtsToEnv of 
                                                                                                Nothing -> error "Expected to have location in env!"
                                                                                                -- Vidush  
                                                                                                Just lst -> case lst of
                                                                                                                  -- Vidush: we just take the first variable for now.
                                                                                                                  -- TODO: Check this
                                                                                                                  (var, _,_, _):xs -> case M.lookup var tenv of 
                                                                                                                                        Nothing -> dbgTrace (minChatLvl) "Print var in Nothing branch 3523: " dbgTrace (minChatLvl) (sdoc (var, loc)) dbgTrace (minChatLvl) "End Print var in Nothing branch 3523.\n"  pure $ [(var, [])]
                                                                                                                                        Just ty -> case (unTy2 ty) of 
                                                                                                                                                      _ -> do 
                                                                                                                                                                     deref_val <- gensym "deref"
                                                                                                                                                                     pure $ [(deref_val, [(deref_val, [], CursorTy, Ext $ DerefMutCursor var)])]
                                                                                                                                                      -- CursorTy -> case modality_floc of 
                                                                                                                                                      --                     Just InputMutable -> do deref_val <- gensym "deref"
                                                                                                                                                      --                                             pure $ [(deref_val, [(deref_val, [], CursorTy, Ext $ DerefMutCursor var)])]
                                                                                                                                                      --                     Just OutputMutable -> do deref_val <- gensym "deref"
                                                                                                                                                      --                                              pure $ [(deref_val, [(deref_val, [], CursorTy, Ext $ DerefMutCursor var)])]
                                                                                                                                                      --                     _ -> dbgTrace (minChatLvl) "Print var in Cursor branch 3528: " dbgTrace (minChatLvl) (sdoc (var, loc)) dbgTrace (minChatLvl) "End Print var in Cursor branch 3528.\n" pure $ [(var, [])]
                                                                                                                  [] -> error "Expected to have variable in env!"
                                                            _ -> case (M.lookup (fromLocVarToFreeVarsTy (toLocVar loc)) freeVarToVarEnv) of
                                                                              Just v -> pure $ [(v, [])]
                                                                              Nothing -> error "cursorizeLocExp: GenSoALoc: unexpected field location variable"
                                        -- Here we need to generate indexing operations from the variable
                                        -- There shouldn't be any recursion, since we fully linearized the data type
                                        SoA{} -> let var_for_loc = case (M.lookup (fromLocVarToFreeVarsTy (toLocVar loc)) freeVarToVarEnv) of
                                                                    Just v -> v
                                                                    Nothing -> error "cursorizeLocExp: GenSoALoc: unexpected field location variable"
                                                     loc_ty = getCursorizeTyFromLocVar Nothing useMutableCursorsCall (toLocVar loc)
                                                  in case loc_ty of 
                                                          CursorTy -> pure $ [(var_for_loc, [])]
                                                          CursorArrayTy sz -> do
                                                                              indexing_inst <- foldlM (\new_names i -> do
                                                                                                            new_var <- gensym "unpack"
                                                                                                            return $ new_names ++ [ (new_var, [(new_var, [], CursorTy, (Ext (IndexCursorArray var_for_loc i)))] ) ]
                                                                                                      ) [] [0..(sz - 1)]
                                                                              pure $ indexing_inst
                    )               
                    flocs
            -- We potentially update mLocPtsToEnv env
            let lvar_loc = toLocVar lvararg 
            let lvar_name = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lvar_loc)
            let mLocPtsToEnv' = findMutSoALocPtsToSoALoc lvar_loc lvar_name mLocPtsToEnv 
            let res' = concatMap (\r -> r) res
            let field_vars = map fst res'
            let new_insts = concatMap snd res'
            let rhs = mkMakeCursorArrayDbg lvar_name ([dcloc_var] ++ field_vars)
            dbgTrace (minChatLvl) "Print freeVarEnv GenSoALoc:" dbgTrace (minChatLvl) (sdoc (freeVarToVarEnv)) dbgTrace (minChatLvl) "End freeVarEnv\n" return $ (Right (rhs, new_insts, [], tenv, senv),  mLocPtsToEnv', mLocOldValEnv)
          -- _ -> do 
          --   {- VS: TODO: don't use unwrap loc var and keep an env mapping loc to its variable name in the program -}
          --   let dcloc_var = case (M.lookup (fromLocVarToFreeVarsTy (toLocVar dloc)) freeVarToVarEnv) of
          --                     Just v -> v
          --                     Nothing -> error "cursorizeLocExp: GenSoALoc: unexpected data constructor location variable"
          --   res <-
          --         mapM
          --           (\(_, loc) -> case (toLocVar loc) of 
          --                               Single{} -> case (M.lookup (fromLocVarToFreeVarsTy (toLocVar loc)) freeVarToVarEnv) of
          --                                                                     Just v -> pure $ [(v, [])]
          --                                                                     Nothing -> error "cursorizeLocExp: GenSoALoc: unexpected field location variable" 
          --                               -- Here we need to generate indexing operations from the variable
          --                               -- There shouldn't be any recursion, since we fully linearized the data type
          --                               SoA{} -> let var_for_loc = case (M.lookup (fromLocVarToFreeVarsTy (toLocVar loc)) freeVarToVarEnv) of
          --                                                           Just v -> v
          --                                                           Nothing -> error "cursorizeLocExp: GenSoALoc: unexpected field location variable"
          --                                            loc_ty = getCursorizeTyFromLocVar Nothing useMutableCursorsCall (toLocVar loc)
          --                                         in case loc_ty of 
          --                                                 CursorTy -> pure $ [(var_for_loc, [])]
          --                                                 CursorArrayTy sz -> do
          --                                                                     indexing_inst <- foldlM (\new_names i -> do
          --                                                                                                   new_var <- gensym "unpack"
          --                                                                                                   return $ new_names ++ [ (new_var, [(new_var, [], CursorTy, (Ext (IndexCursorArray var_for_loc i)))] ) ]
          --                                                                                             ) [] [0..(sz - 1)]
          --                                                                     pure $ indexing_inst
          --           )               
          --           flocs
          --   let res' = concatMap (\r -> r) res
          --   let field_vars = map fst res'
          --   let new_insts = concatMap snd res'
          --   let rhs = Ext $ MakeCursorArray (1 + length field_vars) ([dcloc_var] ++ field_vars)
          --   dbgTrace (minChatLvl) "Print freeVarEnv GenSoALoc:" dbgTrace (minChatLvl) (sdoc (freeVarToVarEnv)) dbgTrace (minChatLvl) "End freeVarEnv\n" return $ (Right (rhs, new_insts, [], tenv, senv),  mLocPtsToEnv, mLocOldValEnv)

    _ -> error $ "cursorizeLocExp: Unexpected locExp: " ++ sdoc locExp

findMutSoALocPtsToSoALoc :: LocVar -> Var -> MutableLocPtsToEnv -> MutableLocPtsToEnv
findMutSoALocPtsToSoALoc locvar locsvar env = 
  let dconloc = getDconLoc locvar 
      fldlocs = getAllFieldLocsSoA locvar
      dconlocmut = checkIfLocIsPointedToByOutputMutLoc dconloc env
      fldlocs' = map (\(k, fl) -> (k, checkIfLocIsPointedToByOutputMutLoc fl env)) fldlocs
      isNull = foldr (\s a -> case s of 
                                Nothing -> True 
                                _ -> a           
                     ) False ([dconlocmut] ++ (map snd fldlocs'))
    in if isNull 
       then dbgTrace (minChatLvl) "Print in findMutSoALocPtsToSoALoc: " dbgTrace (minChatLvl) (sdoc (dconloc, dconlocmut, fldlocs, fldlocs')) dbgTrace (minChatLvl) "End in findMutSoALocPtsToSoALoc!\n" env -- error $ "Did not expected null!" ++ show (dconloc, dconlocmut, fldlocs, fldlocs')
       else 
        let constructed_soa_loc = SoA (unwrapLocVar $ fromJust dconlocmut) (map (\(k, l) -> (k, fromJust l)) fldlocs')
            -- check is constructed_soa_loc is in the env
            mutsoa = M.lookup constructed_soa_loc env
         in case mutsoa of 
                    Nothing -> dbgTrace (minChatLvl) "Print in findMutSoALocPtsToSoALoc: " dbgTrace (minChatLvl) (sdoc (dconloc, dconlocmut, fldlocs, fldlocs')) dbgTrace (minChatLvl) "End in findMutSoALocPtsToSoALoc!\n" env -- error $ "expected mutloc in env!!" ++ show (constructed_soa_loc)
                    Just ls -> case ls of
                             (_var, _l, r, aliases):xs -> dbgTrace (minChatLvl) "Print in findMutSoALocPtsToSoALoc: " dbgTrace (minChatLvl) (sdoc (dconloc, dconlocmut, fldlocs, fldlocs')) dbgTrace (minChatLvl) "End Not null in findMutSoALocPtsToSoALoc!\n" updateMutableLocPtsToEnv constructed_soa_loc env (locsvar, Just locvar, r, S.insert _var aliases) False
                             [] -> error "Expected to have variable keys in env!\n"

cursorizeRegExp :: MutableLocPtsToEnv -> MutableLocOldValueEnv -> Bool -> M.Map FreeVarsTy Var -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> RegVar -> RegExp -> PassM (Either DepEnv (Exp3, [Binds Exp3], TyEnv Var Ty2, SyncEnv), MutableLocPtsToEnv, MutableLocOldValueEnv)
cursorizeRegExp mLocPtsToEnv mLocOldValEnv useMutableCursorsCall freeVarToVarEnv denv tenv senv lvar regExp =
  case regExp of
    GetDataConRegSoA loc -> do
      let loc_from_logarg = toLocVar loc
          modality = getModality loc
          loc_region = toRegVar loc
          reg_from_loc = fromLocVarToRegVar loc_from_logarg
          reg_var = case (M.lookup (fromRegVarToFreeVarsTy reg_from_loc) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show regExp ++ "," ++ (show (reg_from_loc)) ++ ")" ++ show freeVarToVarEnv
          -- rhs = Ext $ IndexCursorArray reg_var 0
          lvar_name = case (M.lookup (fromRegVarToFreeVarsTy lvar) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show regExp ++ "," ++ (show (lvar)) ++ ")" ++ show freeVarToVarEnv
      (mLocPtsToEnv', mLocOldValEnv', rhs, additional_bnds) <- case modality of 
                                                Just OutputMutable -> do 
                                                                      let rhs_tmp = Ext $ IndexCursorArray reg_var 0 
                                                                      if not (M.member loc_from_logarg mLocOldValEnv)
                                                                      then do 
                                                                          cpy <- gensym "cpy"
                                                                          let cpy_ty = getCursorizeTyFromLocVar'' modality useMutableCursorsCall loc_from_logarg
                                                                          -- (v, [], locs_ty3, Ext $ InitCursor locs_ty3),
                                                                          -- ("_", [], ProdTy [], Ext (MemCpy v var_dcon_next locs_ty3))
                                                                          let memcpy_intr = [(cpy, [], cpy_ty, Ext $ InitCursor cpy_ty), ("_", [], ProdTy [], Ext $ MemCpy cpy reg_var cpy_ty)]
                                                                          let mLocPtsToEnv_i = updateMutableLocPtsToEnv loc_from_logarg mLocPtsToEnv (cpy, Nothing, Just loc_region, S.empty) False
                                                                          let mLocOldValEnv_i =  M.insert loc_from_logarg (cpy, Nothing, Just loc_region, S.empty) mLocOldValEnv
                                                                          pure (mLocPtsToEnv_i, mLocOldValEnv_i, rhs_tmp, memcpy_intr)  
                                                                      else pure (mLocPtsToEnv, mLocOldValEnv, rhs_tmp, []) 
                                                                      
                                                _ -> do
                                                     let rhs_tmp = Ext $ IndexCursorArray reg_var 0  
                                                     pure (mLocPtsToEnv, mLocOldValEnv, rhs_tmp, [])
      
      if isBound reg_var tenv
            then pure $ (Right (rhs, [], tenv, senv), mLocPtsToEnv', mLocOldValEnv')
            -- CursorArrayTy (1 + length (getAllFieldLocsSoA loc_from_logarg))
            -- VS: Hack: We always want to get a reference to the region.
            else pure $ (Left $ M.insertWith (++) (fromRegVarToFreeVarsTy reg_from_loc) (additional_bnds ++ [(lvar_name, [], CursorTy, rhs)]) denv, mLocPtsToEnv', mLocOldValEnv')
    GetFieldRegSoA i loc -> do
      {- VS: TODO: don't use unwrap loc var and keep an env mapping loc to its variable name in the program -}
      let loc_from_locarg = toLocVar loc
          field_locs = getAllFieldLocsSoA loc_from_locarg
          reg_from_loc = fromLocVarToRegVar loc_from_locarg
          loc_var = case (M.lookup (fromRegVarToFreeVarsTy reg_from_loc) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error "cursorizeRegExp: GetFieldRegSoA: unexpected location variable"
          field_loc = case L.lookup i field_locs of
            Just loc -> loc
            Nothing -> error "cursorizeRegExp: GetFieldLocSoA: field location not found!"
          field_loc_elem = (i, field_loc)
          elem_idx = case (L.elemIndex field_loc_elem field_locs) of
            Just idx -> idx
            Nothing -> error "cursorizeRegExp: GetFieldLocSoA: field location not found!"
          lvar_name = case (M.lookup (fromRegVarToFreeVarsTy lvar) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error $ "cursorizeRegExp: GetDataConRegSoA: unexpected location variable: " ++ "(" ++ show regExp ++ "," ++ (show (lvar)) ++ ")" ++ show freeVarToVarEnv
          -- {- VS : We add one since the data constructor is reserved as the first element in the cursor Array -}
      (rhs, additional_lets) <- case field_loc of 
                                            Single{} -> do
                                                        let (start, end, _) = getIndexPositionOfSoALocVar useMutableCursorsCall Nothing field_locs field_loc   
                                                        return $ (Ext $ IndexCursorArray loc_var start, [])
                                            SoA _ fregs -> do
                                                           let CursorArrayTy sz = getCursorizeTyFromLocVar Nothing useMutableCursorsCall field_loc
                                                           let (start, end, _) = getIndexPositionOfSoALocVar useMutableCursorsCall Nothing field_locs field_loc  
                                                           --let start = L.elemIndex (i, field_loc) field_locs
                                                           --let start_val = fromJustDef (-1) start
                                                           res <- foldlM (\bnds i -> do 
                                                                                           new_var <- gensym "unpack_loc"
                                                                                           return $ bnds ++ [ (new_var, (new_var, [], CursorTy, Ext $ IndexCursorArray loc_var i)) ]
                                                                              ) [] [(start)..(end-1)]
                                                           let vars = map fst res
                                                           let bnds = map snd res
                                                           return $ (mkMakeCursorArrayDbg lvar_name vars, bnds)
      if isBound loc_var tenv
            then pure $ (Right (rhs, additional_lets, tenv, senv), mLocPtsToEnv, mLocOldValEnv)
            else pure (Left $ M.insertWith (++) (fromRegVarToFreeVarsTy reg_from_loc) (additional_lets ++ [(lvar_name, [], CursorTy, rhs)]) denv, mLocPtsToEnv, mLocOldValEnv)
    GenSoAReg dloc flocs -> do
      {- VS: TODO: don't use unwrap loc var and keep an env mapping loc to its variable name in the program -}
      let dcloc_var = case (M.lookup (fromRegVarToFreeVarsTy (fromLocVarToRegVar $ toLocVar dloc)) freeVarToVarEnv) of
            Just v -> v
            Nothing -> error "cursorizeRegExp: GenSoAReg: unexpected data constructor location variable"
      res <-
            mapM
              (\(_, loc) -> case (fromLocVarToRegVar $ toLocVar loc) of 
                                  SingleR{} -> case (M.lookup (fromRegVarToFreeVarsTy (fromLocVarToRegVar $ toLocVar loc)) freeVarToVarEnv) of
                                                                        Just v -> pure $ [(v, [])]
                                                                        Nothing -> error "cursorizeLocExp: GenSoALoc: unexpected field location variable" 
                                  -- Here we need to generate indexing operations from the variable
                                  -- There shouldn't be any recursion, since we fully linearized the data type
                                  SoARv{} -> let var_for_loc = case (M.lookup (fromRegVarToFreeVarsTy (fromLocVarToRegVar $ toLocVar loc)) freeVarToVarEnv) of
                                                              Just v -> v
                                                              Nothing -> error "cursorizeLocExp: GenSoALoc: unexpected field location variable"
                                                 loc_ty = getCursorizeTyFromRegVar Nothing useMutableCursorsCall (fromLocVarToRegVar $ toLocVar loc)
                                             in case loc_ty of 
                                                    CursorTy -> pure $ [(var_for_loc, [])]
                                                    CursorArrayTy sz -> do
                                                                         indexing_inst <- foldlM (\new_names i -> do
                                                                                                       new_var <- gensym "unpack"
                                                                                                       return $ new_names ++ [ (new_var, [(new_var, [], CursorTy, (Ext (IndexCursorArray var_for_loc i)))] ) ]
                                                                                                ) [] [0..(sz - 1)]
                                                                         pure $ indexing_inst
              )               
              flocs
      let res' = concatMap (\r -> r) res
      let field_vars = map fst res'
      let lvar_loc = L2.fromRegVarToLocVar lvar
      let lvar_name = getVarNameFromFreeVar freeVarToVarEnv (fromRegVarToFreeVarsTy lvar)
      let mLocPtsToEnv' = findMutSoALocPtsToSoALoc lvar_loc lvar_name mLocPtsToEnv
      let new_insts = concatMap snd res'
          rhs = mkMakeCursorArrayDbg lvar_name ([dcloc_var] ++ field_vars)
       in dbgTrace (minChatLvl) "Print freeVarEnv GenSoAReg:" dbgTrace (minChatLvl) (sdoc (freeVarToVarEnv)) dbgTrace (minChatLvl) "End freeVarEnv\n" pure $  (Right (rhs, new_insts, tenv, senv), mLocPtsToEnv', mLocOldValEnv) 
   

findSoAParent :: FreeVarsTy -> M.Map FreeVarsTy Var -> Maybe FreeVarsTy
findSoAParent fvar freeVarEnv = case fvar of
  R r ->
    let allKeys = M.keys freeVarEnv
        parent =
          foldr
            ( \k acc -> case k of
                R r' -> case (findRegInRegion r' r) of
                  Just regg -> Just regg
                  Nothing -> acc
                FL l -> acc
                V v -> acc
            )
            Nothing
            allKeys
     in case parent of
          Just p -> Just $ R p
          Nothing -> Nothing
  FL l -> Nothing
  V v -> Nothing

-- findSoAParentHelper :: FreeVarsTy -> FreeVarsTy -> Maybe FreeVarsTy
-- findSoAParentHelper a b = case (a, b) of
--                                 (R r1, R r2) -> if r1 == r2
--                                                 then Just a
--                                                 else case r1 of
--                                                       SingleR _ -> Nothing
--                                                       SoAR dcReg fieldRegs -> let check_fields = map (\r -> if r == r2 then Just r else Nothing) fieldRegs
--                                                                                 in
--                                 FL l ->
--                                 V v ->

findRegInRegion :: RegVar -> RegVar -> Maybe RegVar
findRegInRegion r1 r2 =
  if r1 == r2
    then Just r1
    else case r1 of
      SingleR _ -> Nothing
      SoARv dcReg fieldRegs -> case r2 of
        SingleR _ -> if dcReg == r2 then Just r1 else Nothing
        SoARv _ _ ->
          let found = foldr (\(_, fr) acc -> if fr == r2 then Just r1 else acc) Nothing fieldRegs
           in found

-- ASSUMPTIONS:
-- (1) `locs` has [in_regions, out_regions, in_locs, out_locs] for the function.
--     But after Cursorize, the calling convention changes so that input
--     locations appear last. Plus, `arg` would supply those. So we can
--     safely drop them from `locs`.
--
-- (2) We update `arg` so that all packed values in it only have start cursors.
cursorizeAppE :: MutableLocPtsToEnv -> MutableLocOldValueEnv -> Bool -> Bool -> Bool -> M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Exp2 -> PassM (Exp3, M.Map FreeVarsTy Var, MutableLocPtsToEnv, MutableLocOldValueEnv)
cursorizeAppE m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv ex =
  case ex of
    AppE f _cty locs args -> do
      let (fnTy, fmeta) = case M.lookup f fundefs of
            Just g -> (funTy g, funMeta g)
            Nothing -> error $ "Unknown function: " ++ sdoc f
          in_tys = arrIns fnTy
          inLocs = inLocVars fnTy
          numRegs = length (outRegVars fnTy) + length (L2.outRegVarsMutable fnTy) + length (inRegVars fnTy)
          -- Drop input locations, but keep everything else
          outs = (L.take numRegs locs) ++ (L.drop numRegs $ L.drop (length inLocs) $ locs)
          isFunctionRec = case funRec fmeta of
                                        TailRec -> True
                                        Rec -> True
                                        _ -> False
          calleeHasPackedInput = any (hasPacked . unTy2) (arrIns fnTy)
          calleeHasPackedOutput = hasPacked (unTy2 (arrOut fnTy))
          calleeHasPackedLocations = numRegs > 0 || not (null (locVars fnTy)) || not (null (locRets fnTy)) || not (null locs)
          calleeHasMutableLocations =
            not (null (L2.outRegVarsMutable fnTy))
            || any (isMutModality . lrmMode) (L2.inRegVars' fnTy ++ locVars fnTy)
            || any (\(EndOf lrm) -> isMutModality (lrmMode lrm)) (locRets fnTy)
          useMutForCall = isFunctionRec && (useMutableCursorsCall || calleeHasMutableLocations)
          cursorizeCallInTy ty =
            case ty of
              IntTy -> IntTy
              CharTy -> CharTy
              FloatTy -> FloatTy
              SymTy -> SymTy
              BoolTy -> BoolTy
              ProdTy ls -> ProdTy $ L.map cursorizeCallInTy ls
              SymDictTy ar _ty -> SymDictTy ar CursorTy
              PDictTy k v -> PDictTy (cursorizeCallInTy k) (cursorizeCallInTy v)
              PackedTy _ l ->
                if useMutForCall
                then case l of
                       Single{} -> MutCursorTy
                       SoA{} -> getCursorizeTyFromLocVar'' Nothing useMutForCall l
                else getCursorizeTyFromLocVar'' Nothing useMutForCall l
              VectorTy el_ty -> VectorTy $ cursorizeCallInTy el_ty
              ListTy el_ty -> ListTy $ cursorizeCallInTy el_ty
              PtrTy -> PtrTy
              CursorTy -> CursorTy
              MutCursorTy -> MutCursorTy
              CursorArrayTy size -> CursorArrayTy size
              ArenaTy -> ArenaTy
              SymSetTy -> SymSetTy
              SymHashTy -> SymHashTy
              IntHashTy -> IntHashTy
          cursorizedCallInputTys =
            let outRegs =
                  L.map
                    (\r -> getCursorizeTyFromRegVar'' (Just Output) useMutForCall r)
                    (outRegVars fnTy)
                  ++ L.map
                    (\r -> getCursorizeTyFromRegVar'' (Just OutputMutable) useMutForCall r)
                    (L2.outRegVarsMutable fnTy)
                outCurs =
                  filter (\(LRM _ _ m) -> m == Output || m == OutputMutable) (locVars fnTy)
                outCurTys =
                  L.map
                    (\(LRM l _ m) -> getCursorizeTyFromLocVar'' (Just m) useMutForCall l)
                    outCurs
                inRegs =
                  L.map
                    (\(LRM _ r m) -> getCursorizeTyFromRegVar'' (Just m) useMutForCall (regionToVar r))
                    (L2.inRegVars' fnTy)
                cursorizedInTys = inRegs ++ outRegs ++ outCurTys ++ map unTy2 in_tys
             in map (stripTyLocs . cursorizeCallInTy) cursorizedInTys
          argTys = dbgTrace (minChatLvl) "Print locs in cursorize AppE " dbgTrace (minChatLvl) (sdoc (f, locs)) dbgTrace (minChatLvl) "End cursorize AppE\n" map (gRecoverType ddfs (Env2 tenv M.empty)) args
          -- In mutable calls, the callee's input EndOfReg argument is the
          -- end of the packed value, not necessarily the current chunk/region end.
          -- Recover the value end (`end_x`) from the corresponding packed argument.
          inputValueEndsByEndReg =
            let locEndRegs =
                  M.fromList
                    [ (lremLoc lrm, lremEndReg lrm)
                    | Loc lrm <- locs
                    , lremMode lrm == L2.Input || lremMode lrm == L2.InputMutable
                    ]
                packedArgEnd ty arg =
                  case (unTy2 ty, arg) of
                    (PackedTy _ loc, VarE v) ->
                      case loc of
                        Single{} -> do
                          endReg <- M.lookup loc locEndRegs
                          pure (endReg, toEndV v)
                        _ -> Nothing
                    _ -> Nothing
             in M.fromList $ Mb.mapMaybe (uncurry packedArgEnd) (zip argTys args ++ zip in_tys args)
          sameRegSkeleton r1 r2 =
            case (r1, r2) of
              (SingleR _, SingleR _) -> True
              (SoARv dc1 fieldRegs1, SoARv dc2 fieldRegs2) ->
                sameRegSkeleton dc1 dc2
                  && length fieldRegs1 == length fieldRegs2
                  && and
                    ( zipWith
                        (\(key1, reg1) (key2, reg2) -> key1 == key2 && sameRegSkeleton reg1 reg2)
                        fieldRegs1
                        fieldRegs2
                    )
              _ -> False
          findReusableOutputEndReg acc wantedReg =
            if useMutForCall
              then
                let compatibleOutReg = \locarg ->
                      case locarg of
                        Loc LREM {lremEndReg} ->
                          if sameRegSkeleton wantedReg lremEndReg
                            then M.lookup (fromRegVarToFreeVarsTy lremEndReg) acc
                            else Nothing
                        _ -> Nothing
                 in L.find (/= "") $ Mb.mapMaybe compatibleOutReg outs
              else Nothing
      (freeVarToVarEnv', newInsts) <-
        foldrM
          ( \loc (acc, acc') -> do
              let loc_var = fromLocArgToFreeVarsTy loc
              nacc <- case (M.lookup (loc_var) freeVarToVarEnv) of
                Just v -> return (acc, acc')
                Nothing -> case loc_var of
                  R r -> case r of
                    {-Vidush: TODO, the type of this needs to change -}
                    SingleR v -> return $ (M.insert loc_var v acc, acc')
                    SoARv dconReg fieldRegions ->
                      case findReusableOutputEndReg acc r of
                        Just existingRegVar ->
                          return (M.insert loc_var existingRegVar acc, acc')
                        Nothing -> do
                          -- let us try to find if the SoA region belongs to any other SoA region in the environment.
                          let parentRegion = findSoAParent loc_var acc
                          ret <- case parentRegion of
                            Just par_reg -> do
                              let name_par_reg = case (M.lookup par_reg acc) of
                                    Just v -> v
                                    Nothing -> error $ "cursorizeAppE: Did not find an end of region variable for the corresponding parent region.\n\n" ++ show f ++ "\n\n " ++ show r ++ "\n\n " ++ show acc
                              name <- gensym "cursor_reg_ptr"
                              let (R par_reg_inner) = par_reg
                              -- Vidush: TODO, is this right?
                              let (start, end, _) = getIndexPositionOfSoARegVar useMutableCursorsCall Nothing (getAllFieldRegsSoA par_reg_inner) r
                              (_acc, instrs) <- handleIndexingSoARegCursors useMutableCursorsCall (r, name) (start, end) par_reg_inner acc
                              --let instrs = [LetE (name, [], getCursorizeTyFromRegVar r, Ext $ IndexCursorArray (name_par_reg) 1)]
                              let instrs' = map (\i -> LetE i) instrs
                              return $ (M.insert loc_var name _acc, acc' ++ instrs')
                            Nothing -> do
                              (dconReg_var, dcon_insts) <- case (M.lookup (fromRegVarToFreeVarsTy dconReg) acc) of
                                Just v -> return (v, [])
                                Nothing -> do
                                  let parent_dcon_end = findSoAParent (fromRegVarToFreeVarsTy dconReg) acc
                                  name_dcon <- case dconReg of
                                    SingleR s -> return s
                                    SoARv _ _ -> do
                                      dnew_name <- gensym "dcon_end"
                                      return dnew_name
                                  case parent_dcon_end of
                                    Just p -> do
                                      let p_var_name = case (M.lookup p acc) of
                                            Just v -> v
                                            Nothing -> error $ "cursorizeAppE: Did not find an end of region variable for the corresponding parent region.\n\n" ++ show f ++ "\n\n " ++ show r ++ "\n\n " ++ show acc
                                      let instrs = [LetE (name_dcon, [], CursorTy, Ext $ IndexCursorArray (p_var_name) 0)]
                                      return (name_dcon, instrs)

                              -- Nothing -> error $ "cursorizeAppE: Did not find an end of region variable for the corresponding datacon region.\n\n" ++ show f ++ "\n\n " ++ show r ++ "\n\n " ++ show acc
                              (fieldReg_vars, bnds) <-
                                    foldlM
                                      (\(vs, bds) (key, field_reg) -> do 
                                                                        v <- case (M.lookup (fromRegVarToFreeVarsTy field_reg) acc) of
                                                                                            Just vv -> return vv
                                                                                            Nothing -> error "cursorizeAppE: Did not find an end of region variable for the corresponding  field region.\n"
                                                                        case field_reg of 
                                                                              SingleR{} -> do 
                                                                                           pure (vs ++ [v], bds)
                                                                              SoARv{} -> do
                                                                                         --let (start, end, _) = getIndexPositionOfSoARegVar fieldRegions field_reg
                                                                                         let CursorArrayTy _sz = getCursorizeTyFromRegVar Nothing useMutableCursorsCall field_reg
                                                                                         (nvars, bnds) <- foldlM (\(nv, bnd) i -> do 
                                                                                                                    var_n <- gensym "unpack"
                                                                                                                    return (nv ++ [var_n], bnd ++ [(var_n, [], CursorTy, Ext $ IndexCursorArray v i)])  
                                                                                          
                                                                                                        ) ([], []) [0 ..(_sz - 1)]
                                                                                         pure (vs ++ nvars, bds ++ bnds)
                                      )
                                      ([], [])
                                      fieldRegions
                              name <- gensym "cursor_reg_ptr"
                              let tenvWithSoARegBnds =
                                    foldr
                                      (\(v, _, ty, _) env -> M.insert v (MkTy2 (fmap (const (Single (toVar "_soa_reg_bnd_loc"))) ty)) env)
                                      tenv
                                      bnds
                              (cursor_vars, deref_bnds) <- foldlM
                                (\(vs, ds) var ->
                                   case M.lookup var tenvWithSoARegBnds of
                                     Just ty | unTy2 ty == MutCursorTy -> do
                                       deref_var <- gensym "deref_reg"
                                       pure (vs ++ [deref_var], ds ++ [(deref_var, [], CursorTy, Ext $ DerefMutCursor var)])
                                     _ -> pure (vs ++ [var], ds))
                                ([], [])
                                ([dconReg_var] ++ fieldReg_vars)
                              let instrs = dcon_insts ++ (map (\i -> LetE i) bnds) ++ (map (\i -> LetE i) deref_bnds) ++ [LetE (name, [], getCursorizeTyFromRegVar Nothing useMutableCursorsCall r, mkMakeCursorArrayDbg name cursor_vars)]
                              dbgTrace (minChatLvl) "Print Reg: " dbgTrace (minChatLvl) (sdoc (f, dconReg, fieldRegions)) dbgTrace (minChatLvl) "End soa Reg\n" return $ (M.insert loc_var name acc, acc' ++ instrs)
                          pure ret

                  -- may need to generate instructions to fetch correct end of regions here.
                  -- Right now I am just leaving this to one level of nesting, in the future this may need to be recursive.
                  -- let dconReg_var = case (M.lookup (fromRegVarToFreeVarsTy dconReg) acc) of
                  --                         Just v -> v
                  --                         Nothing -> error $ "cursorizeAppE: Did not find an end of region variable for the corresponding datacon region.\n\n" ++ show f ++ "\n\n " ++ show r ++ "\n\n " ++ show acc
                  -- let fieldReg_vars = map (\(key, field_reg) -> case (M.lookup (fromRegVarToFreeVarsTy field_reg) acc) of
                  --                                                                         Just v -> v
                  --                                                                         Nothing -> error "cursorizeAppE: Did not find an end of region variable for the corresponding  field region.\n"
                  --                         ) fieldRegions
                  -- name <- gensym "cursor_reg_ptr"
                  -- let instrs = [LetE (name, [], CursorArrayTy (1 + length fieldReg_vars), Ext $ MakeCursorArray (1 + length fieldReg_vars) ([dconReg_var] ++ fieldReg_vars))]
                  -- dbgTrace (minChatLvl) "Print Reg: " dbgTrace (minChatLvl) (sdoc (f, dconReg, fieldRegions)) dbgTrace (minChatLvl) "End soa Reg\n" return $ (M.insert loc_var name acc, acc' ++ instrs)
                  FL l -> case l of
                    Single v -> return $ (M.insert loc_var v acc, acc')
                    SoA _ _ -> do
                      name <- gensym "cursor_ptr"
                      return $ (M.insert loc_var name acc, acc')
                  V v -> return $ (M.insert loc_var v acc, acc')
              return nacc
          )
          (freeVarToVarEnv, [])
          locs
      let nonSelfCall = case _cty of
                              TailCall -> False
                              _ -> True
      args' <-
        mapM
          ( \(t, a) -> case a of 
                          VarE av -> 
                                  if hasPacked (unTy2 t)
                                    then 
                                      do 
                                        let mut_loc = findMutableLocationPointingToVar av m1
                                        case mut_loc of 
                                              Nothing -> do  
                                                         (a', _, _, _) <- cursorizePackedExp m1 m2 (useMutForCall && isFunctionRec) emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv tenv senv a
                                                         dbgTrace (minChatLvl) "Print args in AppE: " dbgTrace (minChatLvl) (sdoc (a, a', args, (map unTy2 argTys))) dbgTrace (minChatLvl) "End printing in AppE 1.\n" fromDi <$> return a'
                                              Just l ->  do 
                                                         let var = getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy l) 
                                                         (a', _, _, _) <- cursorizePackedExp m1 m2 (useMutForCall && isFunctionRec) emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv tenv senv (VarE var)
                                                         dbgTrace (minChatLvl) "Print args in AppE: " dbgTrace (minChatLvl) (sdoc (a, a', args)) dbgTrace (minChatLvl) "End printing in AppE 2.\n" fromDi <$> return a'
                                    else do 
                                        let mut_loc = findMutableLocationPointingToVar av m1
                                        case mut_loc of 
                                              Nothing -> do  
                                                         (a', _, _, _) <- cursorizeExp m1 m2 (useMutForCall && isFunctionRec) emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv tenv senv a
                                                         dbgTrace (minChatLvl) "Print args in AppE: " dbgTrace (minChatLvl) (sdoc (a, a', args, (map unTy2 argTys))) dbgTrace (minChatLvl) "End printing in AppE 1.\n" return a'
                                              Just l ->  do 
                                                         let var = getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy l) 
                                                         (a', _, _, _) <- cursorizeExp m1 m2 (useMutForCall && isFunctionRec) emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv tenv senv (VarE var)
                                                         dbgTrace (minChatLvl) "Print args in AppE: " dbgTrace (minChatLvl) (sdoc (a, args)) dbgTrace (minChatLvl) "End printing in AppE 2.\n" return a'

                                        
                          _ -> if hasPacked (unTy2 t)
                                    then 
                                      do 
                                        (a', _, _, _) <- cursorizePackedExp m1 m2 (useMutForCall && isFunctionRec) emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv tenv senv a
                                        fromDi <$> return a'
                                    else do 
                                        (a', _, _, _) <- cursorizeExp m1 m2 (useMutForCall && isFunctionRec) emitScalarCountBumps insideTimeIt freeVarToVarEnv' lenv ddfs fundefs denv tenv senv a
                                        return a'
          )
          (zip in_tys args)
      starts0 <- mapM (\(ty, arg) -> giveStarts tenv freeVarToVarEnv useMutForCall insideTimeIt isFunctionRec nonSelfCall m1 m2 ty arg) (zip (map unTy2 argTys) args')
      let varIsAlreadyMutableIn tenvForCall varname =
            case M.lookup varname tenvForCall of
              Just ty ->
                case unTy2 ty of
                  MutCursorTy -> True
                  _ -> checkIfVarIsMutable varname m1
              Nothing -> checkIfVarIsMutable varname m1
      let coerceCursorToMutIfNeeded forceMut tenvForCall argexp =
            if useMutForCall || forceMut
            then case argexp of
                   VarE varname ->
                     if varIsAlreadyMutableIn tenvForCall varname
                     then pure argexp
                     else case M.lookup varname tenvForCall of
                            Just ty ->
                              case unTy2 ty of
                                CursorTy -> do
                                  addr <- gensym "address"
                                  pure $ mkLets [(addr, [], MutCursorTy, Ext $ AddrOfCursor (VarE varname))] (VarE addr)
                                PackedTy {} -> do
                                  addr <- gensym "address"
                                  pure $ mkLets [(addr, [], MutCursorTy, Ext $ AddrOfCursor (VarE varname))] (VarE addr)
                                _ -> pure argexp
                            _ -> pure argexp
                   _ -> pure argexp
            else pure argexp
      let expectedStartParamTys =
            if length cursorizedCallInputTys == length starts0
            then cursorizedCallInputTys
            else map (stripTyLocs . unTy2) in_tys
          forceMutableCursorArgs =
            useMutableCursorsCall && isFunctionRec && null locs
      starts <- mapM
                  (\(paramTy, argexp) ->
                    case paramTy of
                      CursorArrayTy{} -> pure argexp
                      _ ->
                        if hasPacked paramTy || paramTy == MutCursorTy || (forceMutableCursorArgs && paramTy == CursorTy)
                        then coerceCursorToMutIfNeeded (paramTy == MutCursorTy || (forceMutableCursorArgs && paramTy == CursorTy)) tenv argexp
                        else pure argexp
                  )
                  (zip expectedStartParamTys starts0)
      let coerceMutToCursorIfNeeded tenvForCall argexp =
            if useMutForCall || forceMutableCursorArgs
            then pure argexp
            else if not useMutableCursorsCall
            then pure argexp
            else case argexp of
                     VarE varname -> case M.lookup varname tenvForCall of
                                       Just ty -> case (unTy2 ty) of
                                                    MutCursorTy -> do
                                                      deref <- gensym "deref"
                                                      pure $ mkLets [(deref, [], CursorTy, Ext $ DerefMutCursor varname)] (VarE deref)
                                                    _ -> pure argexp
                                       _ -> pure argexp
                     _ -> pure argexp
      starts' <- mapM (coerceMutToCursorIfNeeded tenv) starts
      let hoistCallArgLets arg =
            case arg of
              LetE b@(_, _, _, Ext (DerefMutCursor{})) body ->
                let (bnds, arg') = hoistCallArgLets body
                 in (b : bnds, arg')
              LetE b@(_, _, _, Ext (AddrOfCursor{})) body ->
                let (bnds, arg') = hoistCallArgLets body
                 in (b : bnds, arg')
              _ -> ([], arg)
          mkCallApp callArgs =
            let (callArgBnds, callArgs') = unzip (map hoistCallArgLets callArgs)
             in mkLets (concat callArgBnds) (AppE f _cty [] callArgs')
      let ty3ToCallTy2 ty3 = MkTy2 (fmap (const (Single (toVar "_call_arg_loc"))) ty3)
      -- let loc_var = toLocVar loc
      -- let loc_to_variable = case (M.lookup (fromLocVarToFreeVarsTy loc_var) freeVarToVarEnv) of
      --                          Just v -> v
      --                          Nothing -> error "cursorizeAppE: unexpected location variable"
      bod <- case locs of
            [] -> return $ mkCallApp starts'
            _ -> do
                -- outs is where the output locations are stored. 
                -- Vidush: We need to run through output locations
                -- and see if any outputMutable location points to them.
                -- Since we are doing a function call, once the call 
                -- returns, we need to make sure where the ouputMutable 
                -- location points to. I think the cursorizeLet should handle this.
                (additional_bnds, appe_args) <- foldlM
                    (\(bnds, args) loc -> do
                        let l = toLocVar loc
                            -- check if there is an output mutable location that points to the incoming out location.
                            mutl = checkIfLocIsPointedToByOutputMutLoc l m1
                        case mutl of 
                                  -- we just use the same loc
                                  Nothing -> do 
                                             case (getModality loc) of 
                                                      Nothing -> do
                                                                 let lName = getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc)
                                                                 let mut_l = findMutableLocationPointingToVar lName m1
                                                                 case mut_l of 
                                                                      Nothing ->
                                                                        if useMutForCall
                                                                        then if varIsAlreadyMutableIn tenv lName
                                                                             then return $ (bnds, args ++ [VarE lName])
                                                                             else case M.lookup lName tenv of
                                                                                    Just ty -> case unTy2 ty of
                                                                                                 CursorTy -> do
                                                                                                   address <- gensym "address"
                                                                                                   let address_bnd = [(address, [], MutCursorTy, Ext $ AddrOfCursor (VarE lName))]
                                                                                                   return $ (bnds ++ address_bnd, args ++ [VarE address])
                                                                                                 _ -> return $ (bnds, args ++ [VarE lName])
                                                                                    Nothing -> return $ (bnds, args ++ [VarE lName])
                                                                        else return $ (bnds, args ++ [VarE lName])
                                                                      Just ml -> do 
                                                                                  let mlName = getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy ml)
                                                                                  return $ (bnds, args ++ [VarE mlName])

                                                                 
                                                      Just Input -> do
                                                                    case useMutForCall of 
                                                                             True -> do
                                                                                      let varName =
                                                                                            case loc of
                                                                                              EndOfReg _ _ endReg ->
                                                                                                case M.lookup endReg inputValueEndsByEndReg of
                                                                                                  Just valueEnd -> valueEnd
                                                                                                  Nothing -> getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc)
                                                                                              _ -> getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc)
                                                                                          mut_l_pointing_to_cur = dbgTrace (minChatLvl) "Print in AppE Just Input: " dbgTrace (minChatLvl) (sdoc (varName, loc)) dbgTrace (minChatLvl) "End print in AppE Just Input arg.\n" findMutableLocationPointingToVar varName m1
                                                                                      case mut_l_pointing_to_cur of 
                                                                                                             -- Vidush: Again just getting the first variable
                                                                                                  Just ml -> let (rvar,_,_,_):xs = fromJust $ M.lookup ml m1
                                                                                                              in dbgTrace (minChatLvl) "Print in AppE Just Input: " dbgTrace (minChatLvl) (sdoc (varName, loc, rvar)) dbgTrace (minChatLvl) "End print in AppE Just Input Just ml arg.\n" return $ (bnds, args ++ [VarE rvar])
                                                                                                  Nothing -> do 
                                                                                                              case M.lookup varName tenv of 
                                                                                                                              Nothing -> dbgTrace (minChatLvl) "Print in Nothing case curAppE:  " dbgTrace (minChatLvl) (sdoc (varName, loc)) dbgTrace (minChatLvl) "End in Nothing case curAppE." return $ (bnds, args ++ [VarE (getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc))])
                                                                                                                              Just ty -> dbgTrace (minChatLvl) "Print in Just ty case curAppE:  " dbgTrace (minChatLvl) (sdoc (varName, loc)) dbgTrace (minChatLvl) "End in Just ty case curAppE." do 
                                                                                                                                          case (unTy2 ty) of 
                                                                                                                                                MutCursorTy -> do 
                                                                                                                                                                deref <- gensym "deref"
                                                                                                                                                                let derefInst = [(deref, [], CursorTy, Ext $ DerefMutCursor varName)]
                                                                                                                                                                return (bnds ++ derefInst, args ++ [VarE deref])
                                                                                                                                                CursorArrayTy{} -> return $ (bnds, args ++ [VarE (getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc))]) -- [VarE (getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc))]                 
                                                                                                                                                CursorTy -> return $ (bnds, args ++ [VarE (getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc))])
                                                                             False -> do
                                                                                       let varName = getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc)
                                                                                       case M.lookup varName tenv of
                                                                                              Nothing -> return $ (bnds, args ++ [VarE (getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc))])
                                                                                              Just ty -> case (unTy2 ty) of 
                                                                                                              MutCursorTy ->
                                                                                                                if useMutableCursorsCall
                                                                                                                then do
                                                                                                                  deref <- gensym "deref"
                                                                                                                  let derefInst = [(deref, [], CursorTy, Ext $ DerefMutCursor varName)]
                                                                                                                  return (bnds ++ derefInst, args ++ [VarE deref])
                                                                                                                else return $ (bnds, args ++ [VarE (getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc))])
                                                                                                              CursorTy -> return $ (bnds, args ++ [VarE (getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc))])
                                                                                                              _ -> return $ (bnds, args ++ [VarE (getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc))])

                                                      Just _ -> do
                                                                 let default_loc_name = getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc)
                                                                     value_end_name = case (getModality loc, loc) of
                                                                       (Just L2.InputMutable, EndOfReg _ _ endReg) -> M.lookup endReg inputValueEndsByEndReg
                                                                       _ -> Nothing
                                                                     loc_name = dbgTrace (minChatLvl) "Print in Just _ case: " dbgTrace (minChatLvl) (sdoc (mutl, loc)) dbgTrace (minChatLvl) "End in Just _ case." $
                                                                       Mb.fromMaybe default_loc_name value_end_name
                                                                     mut_l_pointing_to_cur = findMutableLocationPointingToVar loc_name m1 
                                                                  in case  mut_l_pointing_to_cur of 
                                                                                Nothing -> let ty_locName = M.lookup loc_name tenv
                                                                                             in case ty_locName of 
                                                                                                        Nothing -> return $ (bnds, args ++ [VarE (if Mb.isJust value_end_name then default_loc_name else loc_name)]) 
                                                                                                        Just ty -> case (unTy2 ty) of 
                                                                                                                        CursorTy -> do
                                                                                                                                     if useMutForCall && isMutModality' (getModality loc) && not (varIsAlreadyMutableIn tenv loc_name)
                                                                                                                                     then do
                                                                                                                                      address <- gensym "address"
                                                                                                                                      let address_bnd = [(address, [], MutCursorTy, Ext $ AddrOfCursor (VarE loc_name))]
                                                                                                                                      return $ (bnds ++ address_bnd, args ++ [VarE address])
                                                                                                                                     else do return $ (bnds, args ++ [VarE loc_name])
                                                                                                                        MutCursorTy -> return $ (bnds, args ++ [VarE loc_name]) -- [VarE (getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc))]
                                                                                                                        _ -> return $ (bnds, args ++ [VarE loc_name])
                                                                                Just mutl' -> return $ (bnds, args ++ [VarE (getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy mutl'))])
                                                        
                                                        
                                  Just mutl' -> case (isRegionLocArg loc) of 
                                                          False -> let locName = getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy mutl')
                                                                    in dbgTrace (minChatLvl) "Print in false case outs: " dbgTrace (minChatLvl) (sdoc (mutl', loc, locName)) dbgTrace (minChatLvl) "End in false case out." return $ (bnds, args ++ [VarE locName])
                                                                  -- Vidush: Just getting the first value, TODO: Fixme 
                                                          True -> let (rvar,_,_,_):xs = fromJust $ M.lookup mutl' m1 
                                                                    in dbgTrace (minChatLvl) "Print in true case outs: " dbgTrace (minChatLvl) (sdoc (mutl', loc, rvar)) dbgTrace (minChatLvl) "End in true case out." return $ (bnds, args ++ [VarE rvar])
                    ) ([], []) outs
                let tenvWithCallArgs =
                      foldr
                        (\(v, _, ty, _) env -> M.insert v (ty3ToCallTy2 ty) env)
                        tenv
                        additional_bnds
                appe_args'' <- mapM (coerceCursorToMutIfNeeded False tenvWithCallArgs) appe_args
                appe_args' <- mapM (coerceMutToCursorIfNeeded tenvWithCallArgs) appe_args''
                if useMutForCall && any (\loc -> case loc of { Loc LREM{lremMode = m} -> m == Output || m == OutputMutable; _ -> False }) outs
                then do
                  let callArgs = appe_args' ++ starts'
                      (callArgBnds, callArgs') = unzip (map hoistCallArgLets callArgs)
                      endRegArgCount = length [() | EndOfReg{} <- outs]
                      endRegArgs = take endRegArgCount callArgs'
                      appeArgsHoisted = take (length appe_args') callArgs'
                      outputLocArgs = [ (loc, arg) | (loc, arg) <- zip outs appeArgsHoisted, case loc of { Loc LREM{lremMode = m} -> m == Output || m == OutputMutable; _ -> False } ]
                      inputValueArgs = take (length (locRets fnTy)) (reverse callArgs')
                      callArgTyEnv =
                        foldr
                          (\(v, _, ty, _) env -> M.insert v (ty3ToCallTy2 ty) env)
                          tenvWithCallArgs
                          (concat callArgBnds)
                      derefCursorArg :: Var -> Exp3 -> PassM ([(Var, [()], Ty3, Exp3)], Exp3)
                      derefCursorArg prefix arg =
                        case arg of
                          VarE varname ->
                            case M.lookup varname callArgTyEnv of
                              Just ty | unTy2 ty == MutCursorTy -> do
                                deref <- gensym prefix
                                pure ([(deref, [], CursorTy, Ext $ DerefMutCursor varname)], VarE deref)
                              _ -> pure ([], arg)
                          _ -> pure ([], arg)
                  (endRegDerefBnds, endRegVals) <- fmap unzip $ mapM (derefCursorArg "deref_end") endRegArgs
                  (inputDerefBnds, inputEndVals) <- fmap unzip $ mapM (derefCursorArg "deref_input_end") inputValueArgs
                  (packedBnds, packedVals) <- fmap unzip $ mapM
                    (\(loc, arg) -> do
                      let startVar = getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy loc)
                      (derefBnds, endVal) <- derefCursorArg "deref_out" arg
                      pure (derefBnds, MkProdE [VarE startVar, endVal]))
                    outputLocArgs
                  let callRetTy = unitizedPackedMutableTy (arrOut fnTy)
                      callTmpPrefix = case callRetTy of
                        ProdTy [] -> "void_call"
                        _ -> "call"
                  callTmp <- gensym callTmpPrefix
                  let callBind = (callTmp, [], callRetTy, AppE f _cty [] callArgs')
                      callPayload = unitizePackedMutableResult (arrOut fnTy) (VarE callTmp)
                      locResults = endRegVals ++ inputEndVals ++ packedVals
                      callResult =
                        case (locResults, hasPacked (unTy2 (arrOut fnTy)), callPayload) of
                          ([], _, _) -> callPayload
                          (_, True, MkProdE []) -> MkProdE locResults
                          (_, True, _) -> callPayload
                          (_, _, _) -> MkProdE (locResults ++ [callPayload])
                  return $ mkLets additional_bnds $
                           mkLets (concat callArgBnds) $
                           LetE callBind $
                           mkLets (concat endRegDerefBnds ++ concat inputDerefBnds ++ concat packedBnds) callResult
                else return $ mkLets additional_bnds (mkCallApp (appe_args' ++ starts'))
      asserts <-
        foldrM
          ( \loc acc ->
              case loc of
                Loc LREM {lremEndReg, lremLoc} -> do
                  let lremEndRegToVar = case (M.lookup (fromRegVarToFreeVarsTy lremEndReg) freeVarToVarEnv') of
                        Just v -> v
                        Nothing -> error "cursorizeAppE: unexpected location variable"
                  let lremLocToVar = case (M.lookup (fromLocVarToFreeVarsTy lremLoc) freeVarToVarEnv') of
                        Just v -> v
                        Nothing -> error "cursorizeAppE: unexpected location variable"
                  let static_loc_ty = getCursorizeTyFromLocVar''' (getModality loc) useMutableCursorsCall lremLoc
                      static_end_ty = getCursorizeTyFromRegVar''' (getModality loc) useMutableCursorsCall lremEndReg
                      mappedLocTy :: Var -> Ty3 -> Ty3
                      mappedLocTy var fallback =
                        case M.lookup var tenv of
                          Just ty -> stripTyLocs (unTy2 ty)
                          Nothing ->
                            case fallback of
                              CursorArrayTy {} -> CursorTy
                              _ -> fallback
                      mappedEndTy :: Ty3 -> Var -> Ty3 -> Ty3
                      mappedEndTy locTy var fallback =
                        case locTy of
                          CursorArrayTy sz ->
                            case M.lookup var tenv of
                              Just ty ->
                                case stripTyLocs (unTy2 ty) of
                                  CursorArrayTy endSz -> CursorArrayTy endSz
                                  _ -> CursorArrayTy sz
                              Nothing -> CursorArrayTy sz
                          _ ->
                            case M.lookup var tenv of
                              Just ty -> stripTyLocs (unTy2 ty)
                              Nothing -> fallback
                      loc_ty = mappedLocTy lremLocToVar static_loc_ty
                      end_ty = mappedEndTy loc_ty lremEndRegToVar static_end_ty
                      cursorAt :: Ty3 -> Var -> Int -> Var -> PassM (Exp3, Exp3 -> Exp3)
                      cursorAt ty var i prefix =
                        case ty of
                          CursorArrayTy {} -> do
                            cur <- gensym prefix
                            pure (VarE cur, LetE (cur, [], CursorTy, Ext $ IndexCursorArray var i))
                          _ -> pure (VarE var, id)
                      assertCursorVars :: Ty3 -> Var -> Int -> Ty3 -> Var -> Int -> Exp3 -> PassM Exp3
                      assertCursorVars locTy locVar locIdx endTy endVar endIdx acc' = do
                        (loc_exp, bind_loc) <- cursorAt locTy locVar locIdx "chk_loc"
                        (end_exp, bind_end) <- cursorAt endTy endVar endIdx "chk_end"
                        chk <- gensym "chk"
                        pure $
                          bind_loc $
                            bind_end $
                              LetE (chk, [], BoolTy, PrimAppE LtP [loc_exp, end_exp]) $
                                LetE ("_", [], ProdTy [], Ext $ Assert (VarE chk)) $
                                  acc'
                  case (loc_ty, end_ty) of
                    (CursorArrayTy loc_sz, CursorArrayTy end_sz) ->
                      foldrM
                        (\i acc' ->
                            assertCursorVars
                              loc_ty
                              lremLocToVar
                              i
                              end_ty
                              lremEndRegToVar
                              i
                              acc')
                        acc
                        [0 .. min loc_sz end_sz - 1]
                    (CursorArrayTy loc_sz, _) ->
                      foldrM
                        (\i acc' ->
                            assertCursorVars
                              loc_ty
                              lremLocToVar
                              i
                              end_ty
                              lremEndRegToVar
                              0
                              acc')
                        acc
                        [0 .. loc_sz - 1]
                    (_, CursorArrayTy {}) ->
                      assertCursorVars
                        loc_ty
                        lremLocToVar
                        0
                        end_ty
                        lremEndRegToVar
                        0
                        acc
                    _ ->
                      assertCursorVars
                        loc_ty
                        lremLocToVar
                        0
                        end_ty
                        lremEndRegToVar
                        0
                        acc
                _ -> pure acc
          )
          bod
          locs
      dflags <- dbgTrace (minChatLvl) "Print Starts: " dbgTrace (minChatLvl) (sdoc (starts', args')) dbgTrace (minChatLvl) "End in print starts!\n" getDynFlags
      let m1_after_call = if useMutForCall && nonSelfCall
                          then
                            let mutated_locs = Mb.mapMaybe
                                                 (\a -> case a of
                                                          VarE v -> findMutableLocationPointingToVar v m1
                                                          _ -> Nothing)
                                                 args
                            in L.foldr M.delete m1 mutated_locs
                          else m1
      if gopt Opt_RtsDebug dflags
        then do
          asserts' <- foldrM (\exprs body -> pure $ exprs body) asserts newInsts
          pure (asserts', freeVarToVarEnv', m1_after_call, m2)
        else do
          bod' <- dbgTrace (minChatLvl) "Print newInts in cursorizeApp: " dbgTrace (minChatLvl) (sdoc (foldr (\i b -> i b) (VarE "") newInsts, args, args', argTys)) dbgTrace (minChatLvl) "End printing newInts in cursorizeAppE.\n" foldrM (\exprs body -> pure $ exprs body) bod newInsts
          pure (bod', freeVarToVarEnv', m1_after_call, m2)
    _ -> error $ "cursorizeAppE: Unexpected " ++ sdoc ex

{-

Cursorizing projections
~~~~~~~~~~~~~~~~~~~~~~~

There are two ways in which projections can be cursorized:

    let pakd_tup = projE n something in
    let x        = projE 0 pakd_tup in
    let end_x    = projE 1 pakd_tup

    OR

    let x     = projE 0 (projE n something) in
    let end_x = projE 1 (projE n something)

`cursorizeLet` creates the former, while the special case here outputs the latter.
Reason: unariser can only eliminate direct projections of this form.
-}
cursorizeProj :: MutableLocPtsToEnv -> MutableLocOldValueEnv -> Bool -> Bool -> Bool -> M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Exp2 -> PassM (Exp3, M.Map FreeVarsTy Var, MutableLocPtsToEnv, MutableLocOldValueEnv)
cursorizeProj m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeit freeVarToVarEnv lenv isPackedContext ddfs fundefs denv tenv senv ex =
  case ex of
    LetE (v, _locs, ty, rhs@ProjE {}) bod | isPackedTy (unTy2 ty) -> do
      (rhs', freeVarToVarEnv', m1', m2') <- go insideTimeit m1 m2 tenv rhs
      let ty' = gRecoverType ddfs (Env2 tenv M.empty) rhs
          ty'' = cursorizeTy freeVarToVarEnv' m1 m2 useMutableCursorsCall Nothing (unTy2 ty')
          cursorizedToUnit t =
            case t of
              ProdTy [] -> True
              _ -> False
      bnds <-
        case unTy2 ty' of
          PackedTy _ loc | cursorizedToUnit ty'' -> do
            let locTy = getCursorizeTyFromLocVar Nothing False loc
                locTy2 = getCursorizeTyFromLocVar'' Nothing False loc
                locName = getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy loc)
                start = case M.lookup loc m2' of
                          Just (oldStart, _, _, _) -> VarE oldStart
                          Nothing -> VarE locName
            case M.lookup locName tenv of
              Just (MkTy2 MutCursorTy) -> do
                end <- gensym "deref"
                pure [ (v, [], locTy, start),
                       (end, [], locTy, Ext $ DerefMutCursor locName),
                       (toEndV v, [], locTy2, VarE end)
                     ]
              _ ->
                pure [ (v, [], locTy, start),
                       (toEndV v, [], locTy2, VarE locName)
                     ]
          _ | isPackedTy (unTy2 ty') ->
              pure [ (v, [], projValTy ty'', mkProj 0 rhs'),
                     (toEndV v, [], projEndsTy ty'', mkProj 1 rhs')
                   ]
          _ ->
              pure [(v, [], ty'', rhs')]
      let tenv' =
            case unTy2 ty' of
              PackedTy _ loc | cursorizedToUnit ty'' ->
                M.union (M.fromList [(v, ty'), (toEndV v, MkTy2 (getCursorizeTyFromLocVar'' Nothing False loc))]) tenv
              _ | isPackedTy (unTy2 ty') ->
                M.union (M.fromList [(v, ty'), (toEndV v, MkTy2 (projEndsTy (unTy2 ty')))]) tenv
              _ ->
                M.insert v ty' tenv
      (bod', freeVarToVarEnv'', m1', m2') <- go insideTimeit m1 m2 tenv' bod
      return (mkLets bnds bod', M.union freeVarToVarEnv' freeVarToVarEnv'', m1', m2') 
    _ -> error $ "cursorizeProj: Unexpected expression: " ++ sdoc ex
  where
    go intime m1g m2g t x =
      if isPackedContext
        then do 
           (x', freeVarToVarEnv', m1g', m2g') <- cursorizePackedExp m1g m2g useMutableCursorsCall emitScalarCountBumps intime freeVarToVarEnv lenv ddfs fundefs denv t senv x
           return (fromDi x', freeVarToVarEnv', m1g', m2g')
        else cursorizeExp m1g m2g useMutableCursorsCall emitScalarCountBumps intime freeVarToVarEnv lenv ddfs fundefs denv t senv x

{-

Products and projections
~~~~~~~~~~~~~~~~~~~~~~~~

As per the dilated representation, all packed values are (start,end) tuples.
Except fn arguments and pattern matched vars (which are just start cursors).
So instead of using the type from the AST, which will always be `Packed`,
we recover type of RHS in the current type environment using gRecoverType.
If it's just `CursorTy`, this packed value doesn't have an end cursor,
otherwise, the type is `PackedTy{}`, and it also has an end cursor.

-}
cursorizeProd :: MutableLocPtsToEnv -> MutableLocOldValueEnv -> Bool -> Bool -> Bool -> M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Exp2 -> PassM (Exp3, M.Map FreeVarsTy Var, MutableLocPtsToEnv, MutableLocOldValueEnv)
cursorizeProd m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv isPackedContext ddfs fundefs denv tenv senv ex =
  case ex of
    LetE (v, _locs, MkTy2 (ProdTy tys), rhs@(MkProdE ls)) bod -> do
      es <- forM (zip tys ls) $ \(ty, e) -> do
        case ty of
          _ | isPackedTy ty -> do 
                                (e', freeVarToVarEnv', m1', m2') <- cursorizePackedExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv e
                                return (fromDi e', freeVarToVarEnv', m1', m2') 
          _ | hasPacked ty -> do 
                               (e', freeVarToVarEnv', m1', m2') <- cursorizePackedExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv e
                               return (fromDi e', freeVarToVarEnv', m1', m2')
          _ -> cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv e
      let es' = map (\(a, _, _, _) -> a) es
          rhs' = MkProdE es' 
          envs = map (\(_, b, _, _) -> b) es
          m1s' = map (\(_, _, c, _) -> c) es
          m2s' = map (\(_, _, _, d) -> d) es
          ty = gRecoverType ddfs (Env2 tenv M.empty) rhs
          ty' = cursorizeTy freeVarToVarEnv m1 m2 useMutableCursorsCall Nothing (unTy2 ty)
          tenv' = M.insert v ty tenv
      (bod', env1, m1', m2') <- go insideTimeIt m1 m2 tenv' bod
      return (mkLets [(v, [], ty', rhs')] bod', M.unions (envs ++ [env1]), M.unions (m1s' ++ [m1']), M.unions (m2s' ++ [m2']))
    _ -> error $ "cursorizeProj: Unexpected expression: " ++ sdoc ex
  where
    go intime m1 m2 t x =
      if isPackedContext
        then do
           (x', freeVarToVarEnv', m1', m2') <- cursorizePackedExp m1 m2 useMutableCursorsCall emitScalarCountBumps intime freeVarToVarEnv lenv ddfs fundefs denv t senv x
           return (fromDi x', freeVarToVarEnv', m1', m2') 
        else cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps intime freeVarToVarEnv lenv ddfs fundefs denv t senv x

{-

Spawn and sync
~~~~~~~~~~~~~~

This is almost identical to a cursorizeLet case below. Except we bind fewer things
and add fewer things to the type environemnt because we have to wait until the
join point.

-}
cursorizeSpawn :: MutableLocPtsToEnv -> MutableLocOldValueEnv -> Bool -> Bool -> Bool -> M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Exp2 -> PassM (Exp3, M.Map FreeVarsTy Var, MutableLocPtsToEnv, MutableLocOldValueEnv)
cursorizeSpawn m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv isPackedContext ddfs fundefs denv tenv senv ex = do
  case ex of
    LetE (v, locs, MkTy2 ty, (SpawnE fn applocs args)) bod
      | isPackedTy ty -> do
          (rhs', freeVarToVarEnv', m11, m22) <- do 
                  (expr, freeVarToVarEnv', m1', m2') <- cursorizePackedExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv (AppE fn UnknownTailType applocs args)
                  return (fromDi expr, freeVarToVarEnv', m1', m2') 
          let rhs'' = case rhs' of
                AppE fn' _cty applocs' args' -> SpawnE fn' applocs' args'
                _ -> error "cursorizeSpawn"
          fresh <- gensym "tup_packed"
          let ty' = case locs of
                [] -> cursorizeTy freeVarToVarEnv' m11 m22 useMutableCursorsCall Nothing ty
                xs -> ProdTy ([CursorTy | _ <- xs] ++ [cursorizeTy freeVarToVarEnv' m11 m22 useMutableCursorsCall Nothing ty])
              tenv' = M.union (M.fromList [(fresh, MkTy2 ty')]) tenv
              -- L.foldr (\(a,b) acc -> M.insert a b acc) tenv $
              --   [(v, ty),(fresh, ty'),(toEndV v, projTy 1 ty')] ++ [(loc,CursorTy) | loc <- locs]
              -- TyEnv Ty2 and L3 expresssions are tagged with different types
              ty'' = curDict $ stripTyLocs ty'
              fresh_rhs = VarE fresh
              (bnds, pending_bnds) =
                case locs of
                  [] ->
                    ( [(fresh, [], ty'', rhs'')],
                      [ (v, [], projTy 0 ty'', MkTy2 ty, mkProj 0 fresh_rhs),
                        (toEndV v, [], projTy 1 ty'', MkTy2 (projTy 1 ty'), mkProj 1 fresh_rhs)
                      ]
                    )
                  _ ->
                    let nLocs = length locs
                        locBnds =
                          [ ((unwrapLocVar . toLocVar) loc, [], CursorTy, MkTy2 CursorTy, mkProj n fresh_rhs)
                          | (loc, n) <- zip locs [0 ..]
                          ]
                        bnds' = [(fresh, [], ty'', rhs'')]
                        pending_bnds' =
                          [ (v, [], projTy 0 $ projTy nLocs ty'', MkTy2 ty, mkProj 0 $ mkProj nLocs fresh_rhs),
                            (toEndV v, [], projTy 1 $ projTy nLocs ty'', MkTy2 (projTy 0 $ projTy nLocs ty'), mkProj 1 $ mkProj nLocs fresh_rhs)
                          ]
                            ++ locBnds
                     in (bnds', pending_bnds')
          case M.lookup (fromVarToFreeVarsTy (toEndV v)) denv of
            Just xs -> error $ "cursorizeSpawn todo: " ++ sdoc xs
            Nothing -> return ()
          let senv' = M.insert v pending_bnds senv
          (bod', freeVarToVarEnv'', m11', m22') <- go insideTimeIt m11 m22 tenv' senv' bod
          let bod'' = updateAvailVars [v] [fresh] bod'
          return (mkLets bnds bod'', M.union freeVarToVarEnv' freeVarToVarEnv'', m11', m22')
      | hasPacked ty -> do
          (rhs', freeVarToVarEnv', m11, m22) <- do 
                   (expr, freeVarToVarEnv', m1', m2') <- cursorizePackedExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv (AppE fn _cty applocs args)
                   return (fromDi expr, freeVarToVarEnv', m1', m2') 
          let rhs'' = case rhs' of
                AppE fn' _ applocs' args' -> SpawnE fn' applocs' args'
                _ -> error $ "cursorizeSpawn: this should've been an AppE. Got" ++ sdoc rhs'
          fresh <- gensym "tup_haspacked"
          let ty' = case locs of
                [] -> cursorizeTy freeVarToVarEnv' m11 m22 useMutableCursorsCall Nothing ty
                xs -> ProdTy ([CursorTy | _ <- xs] ++ [cursorizeTy freeVarToVarEnv' m1 m2 useMutableCursorsCall Nothing ty])
              ty'' = stripTyLocs ty'
              tenv' = M.insert v (MkTy2 ty) tenv
          case locs of
            [] -> do 
              (bod', freeVarToVarEnv'', m11', m22') <- go insideTimeIt m11 m22 tenv' senv bod
              return (LetE (v, [], ty'', rhs'') bod', M.union freeVarToVarEnv' freeVarToVarEnv'', m11', m22')
            _ -> do
              let (bnds, pending_bnds) =
                    ( [(fresh, [], ty'', rhs'')],
                      [((unwrapLocVar . toLocVar) loc, [], CursorTy, MkTy2 CursorTy, ProjE n (VarE fresh)) | (loc, n) <- (zip locs [0 ..])]
                        ++ [(v, [], projTy (length locs) ty'', MkTy2 ty, ProjE (length locs) (VarE fresh))]
                    )
                  senv' = M.insert v pending_bnds senv
              (bod', freeVarToVarEnv'', m11', m22') <- go insideTimeIt m11 m22 tenv' senv' bod
              return (mkLets bnds bod', M.union freeVarToVarEnv' freeVarToVarEnv'', m11', m22') 
      | otherwise -> do
          (rhs', freeVarToVarEnv', m1', m2') <- cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv (AppE fn UnknownTailType applocs args)
          let rhs'' = case rhs' of
                AppE fn' _ applocs' args' -> SpawnE fn' applocs' args'
                _ -> error "cursorizeSpawn"
          case locs of
            [] -> do 
                   (bod', freeVarToVarEnv'', m1'', m2'') <- go insideTimeIt m1' m2' (M.insert v (MkTy2 ty) tenv) senv bod
                   return (LetE (v, [], curDict $ stripTyLocs ty, rhs'') bod', M.union freeVarToVarEnv'' freeVarToVarEnv', m1'', m2'')
            [loc] -> do
              fresh <- gensym "par_tup_scalar"
              let ty' :: OldTy2
                  ty' = ProdTy ([CursorTy | _ <- locs] ++ [cursorizeTy freeVarToVarEnv' m1' m2' useMutableCursorsCall Nothing ty])
                  tenv' = M.union (M.fromList [(fresh, MkTy2 ty')]) tenv
                  ty'' :: Ty3
                  ty'' = stripTyLocs ty'
                  rhs''' = Di (VarE fresh)
                  locs_name = case (M.lookup (fromLocVarToFreeVarsTy (toLocVar loc)) freeVarToVarEnv) of
                    Just v' -> v'
                    Nothing -> error "cursorizeSpawn: unexpected location variable"
                  pending_bnds =
                    [ (locs_name, [], projTy 0 ty'', MkTy2 (projTy 0 ty'), projVal rhs'''),
                      -- [2022.09.21]: Shouldn't this be projTy 1 ty'?
                      (v, [], projTy 1 ty'', MkTy2 (projTy 1 ty'), projEnds rhs''')
                    ]
                  senv' = M.insert v pending_bnds senv
              (bod', freeVarToVarEnv'', m1'', m2'') <- go insideTimeIt m1' m2' tenv' senv' bod
              return (mkLets [(fresh, [], ty'', rhs'')] bod', M.union freeVarToVarEnv' freeVarToVarEnv'', m1'', m2'')
            _ -> error "TODO: cursorizeSpawn"
    _ -> error "cursorizeSpawn: Unbound SpawnE"
  where
    go inTimeIt m1g m2g t s x =
      if isPackedContext
        then do 
            (x', freeVarToVarEnv', m1g', m2g') <- cursorizePackedExp m1g m2g useMutableCursorsCall emitScalarCountBumps inTimeIt freeVarToVarEnv lenv ddfs fundefs denv t s x
            return (fromDi x', freeVarToVarEnv', m1g', m2g')
        else cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps inTimeIt freeVarToVarEnv lenv ddfs fundefs denv t s x

cursorizeSync :: MutableLocPtsToEnv -> MutableLocOldValueEnv -> Bool -> Bool -> Bool -> M.Map FreeVarsTy Var -> M.Map Var (Maybe LocVar) -> Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Var Ty2 -> SyncEnv -> Exp2 -> PassM (Exp3, M.Map FreeVarsTy Var, MutableLocPtsToEnv, MutableLocOldValueEnv)
cursorizeSync m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv isPackedContext ddfs fundefs denv tenv senv ex = do
  case ex of
    LetE (v, _locs, MkTy2 ty, SyncE) bod -> do
      let pending_bnds = concat (M.elems senv)
          tenv' = foldr (\(v1, _, _, ty2, _) env -> M.insert v1 ty2 env) tenv pending_bnds
          -- Discharge bindings that depending on the join point.
          bnds = map (\(a, b, c, _, e) -> (a, b, c, e)) pending_bnds
          bnds' = (v, [], stripTyLocs ty, SyncE) : bnds
      (bod', freeVarToVarEnv', m1', m2') <- go insideTimeIt m1 m2 tenv' bod
      return (mkLets bnds' bod', freeVarToVarEnv', m1', m2')
    _ -> error "cursorizeSpawn: Unbound SyncE"
  where
    go intime m1g m2g t x =
      if isPackedContext
        then do 
           (x', freeVarToVarEnv', m1g', m2g') <- cursorizePackedExp m1g m2g useMutableCursorsCall emitScalarCountBumps intime freeVarToVarEnv lenv ddfs fundefs denv t M.empty x
           return (fromDi x', freeVarToVarEnv', m1g', m2g') 
        else cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps intime freeVarToVarEnv lenv ddfs fundefs denv t M.empty x

{-

Cursorizing let expressions
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Process RHS and bind the following cursors

     v     -> start_write
     end_v -> end_write
     loc   -> end_read     (only if it's available)

An expression returning packed value can either be a `DataConE` or a `AppE`.
DataConE returns a (start_write,end_write) tuple whereas
AppE returns (end_read,end_write).

So we cannot always rely on the RHS to return a start_write cursor.
But since the types of all packed expressions are already annotated with locations,
we can take a shortcut here and directly bind `v` to the tagged location.

Other bindings are straightforward projections of the processed RHS.

-}
packedMutableLetReturnsUnit :: FunDefs2 -> MutableLocPtsToEnv -> LocVar -> Exp2 -> Bool
packedMutableLetReturnsUnit fundefs mutLocs startLoc rhs =
  case rhs of
    DataConE _ _ _ -> False
    AppE f _ _ _ ->
      case M.lookup f fundefs of
        Just FunDef{funTy, funMeta} ->
          isRecursiveFun (funRec funMeta) && hasPacked (unTy2 (arrOut funTy))
        Nothing -> False
    VarE _ -> False
    _ -> False
  where
    isRecursiveFun TailRec = True
    isRecursiveFun Rec = True
    isRecursiveFun _ = False

cursorizeLet ::
  MutableLocPtsToEnv -> 
  MutableLocOldValueEnv ->
  Bool ->
  Bool ->
  Bool -> 
  M.Map FreeVarsTy Var ->
  M.Map Var (Maybe LocVar) ->
  Bool ->
  DDefs Ty2 ->
  FunDefs2 ->
  DepEnv ->
  TyEnv Var Ty2 ->
  SyncEnv ->
  (Var, [LocArg], Ty2, Exp2) ->
  Exp2 ->
  PassM (Exp3, M.Map FreeVarsTy Var, MutableLocPtsToEnv, MutableLocOldValueEnv)
cursorizeLet m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv isPackedContext ddfs fundefs denv tenv senv (v, locs, (MkTy2 ty), rhs) bod
  | isPackedTy ty = do
      let (start_loc, start_var) = case ty of 
                                      PackedTy _ l -> (l, getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy l))
                                      _ -> error "Did not expect a non packed type!"
      let output_type_is_mutable = case M.lookup start_var tenv of 
                                              Nothing -> False 
                                              Just ty -> case (unTy2 ty) of 
                                                                  MutCursorTy -> True 
                                                                  CursorTy -> False
      let useMutableCursors = case rhs of 
                                    AppE f _ _ _ -> let (fnTy, fmeta) = case M.lookup f fundefs of
                                                                                  Just g -> (funTy g, funMeta g)
                                                                                  _ -> error "Expected function definition!!"
                                                     in case funRec fmeta of 
                                                              TailRec -> useMutableCursorsCall
                                                              Rec -> useMutableCursorsCall
                                                              _ -> False
                                    _ -> useMutableCursorsCall
      (_rhs, freeVarToVarEnv', m1', m2') <- dbgTrace (minChatLvl) "Print envs in CursorizeLet: " dbgTrace (minChatLvl) (sdoc (m1, m2)) dbgTrace (minChatLvl) "End printing envs in CursorizeLet.\n" cursorizePackedExp m1 m2 useMutableCursors emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv rhs
      rhsfromdi <- fromDi <$> return _rhs
      -- we need to figure out TimtIt expressions here.
      -- For timeit expressions we need to make sure that we restore the start of the output mutable location.
      -- Not so simple to do this in the IR because we need to deal with inplace mutation of the variables.
      let rhs' = rhsfromdi
      -- let rhs' = case rhsfromdi of 
      --                 TimeIt e ty b -> if M.member start_loc m2'
      --                                  then 
      --                                     let (oldv, _, _) = fromJust $ M.lookup start_loc m2'


      --                                  else rhsfromdi
      --                 _ -> rhsfromdi


      fresh <- dbgTrace (minChatLvl) "Print locs in cursorize Let " dbgTrace (minChatLvl) (sdoc (locs, m1', m2', start_loc, start_var)) dbgTrace (minChatLvl) "End cursorize Let\n" gensym "tup_packed"
      let cursor_ty_locs =
            map
              ( \loc ->
                  let free_var = fromLocArgToFreeVarsTy loc
                      cursorType = case free_var of
                        R r -> getCursorizeTyFromRegVar'' Nothing useMutableCursors r
                        V _ -> error "cursorizeLet: did not expect a variable in locations in a LetE."
                        FL l -> getCursorizeTyFromLocVar'' Nothing useMutableCursors l
                   in cursorType
              )
              locs
      let cursor_ty_locs' =
            map
              ( \loc ->
                  let free_var = fromLocArgToFreeVarsTy loc
                      cursorType :: Ty3 = case free_var of
                        R r -> getCursorizeTyFromRegVar'' Nothing useMutableCursors r
                        V _ -> error "cursorizeLet: did not expect a variable in locations in a LetE."
                        FL l -> getCursorizeTyFromLocVar'' Nothing useMutableCursors l
                   in cursorType
              )
              locs
      -- This part infers the type for the let bound expression. 
      -- In case of tail call optimization, we need to change this type.
      -- Vidush: TODO:         
      let ty' = case locs of
            [] -> cursorizeTy freeVarToVarEnv' m1' m2' useMutableCursors Nothing ty
            xs -> if useMutableCursors
                  then cursorizeTy freeVarToVarEnv' m1' m2' useMutableCursors Nothing ty
                  else ProdTy (cursor_ty_locs ++ [cursorizeTy freeVarToVarEnv' m1' m2' useMutableCursors Nothing ty])
  
          -- -- We need to add the locs correctly in the env.         
          -- tys_in_env = if useMutableCursorsCall 
          --              then [(v, MkTy2 ty), (fresh, MkTy2 ty'), (toEndV v, MkTy2 (projTy 1 ty'))]
          --              else [(v, MkTy2 ty), (fresh, MkTy2 ty'), (toEndV v, MkTy2 (projTy 1 ty'))] 
          --                     ++ map
          --                           ( \loc ->
          --                             let free_var = fromLocArgToFreeVarsTy loc
          --                                 var = case (M.lookup free_var freeVarToVarEnv') of
          --                                                   Just v -> v
          --                                                   Nothing -> error "cursorizeLet: unexpected location variable"
          --                                 cursorType = cursor_ty_locs !! (fromJust $ L.elemIndex loc locs)
          --                               in (var, MkTy2 cursorType)
          --                           ) locs
          end_ty_for_env =
            if useMutableCursors
            then getCursorizeTyFromLocVar'' Nothing useMutableCursors start_loc
            else projTy 1 ty'
          tys_in_env = [(v, MkTy2 ty), (fresh, MkTy2 ty'), (toEndV v, MkTy2 end_ty_for_env)] 
                              ++ map
                                    ( \loc ->
                                      let free_var = fromLocArgToFreeVarsTy loc
                                          var = case (M.lookup free_var freeVarToVarEnv') of
                                                            Just v -> v
                                                            Nothing -> error "cursorizeLet: unexpected location variable"
                                          cursorType = cursor_ty_locs !! (fromJust $ L.elemIndex loc locs)
                                        in (var, MkTy2 cursorType)
                                    ) locs

          
          tenv' = L.foldr (\(a, b) acc -> M.insert a b acc) tenv $ tys_in_env
              

          -- TyEnv Ty2 and L3 expresssions are tagged with different types
          ty'' = curDict $ stripTyLocs ty'
          fresh_ty =
            if useMutableCursors && packedMutableLetReturnsUnit fundefs m1 start_loc rhs
            then ProdTy []
            else ty''
          rhs'' = VarE fresh
          rhsStillReturnsPackedEndpoints = fresh_ty /= ProdTy []
          rhsLocs = case rhs of
            AppE _ _ appLocs _ -> appLocs
            _ -> []
          rhsEndCursorReg locarg = case locarg of
            Loc lrem -> Just (lremEndReg lrem)
            EndWitness lrem _ -> Just (lremEndReg lrem)
            Reg r _ -> Just (toEndVRegVar r)
            EndOfReg _ _ r -> Just r
            EndOfReg_Tagged r -> Just r
          unitizedOutputEndRegBnds =
            if useMutableCursors && not rhsStillReturnsPackedEndpoints
            then
              Mb.mapMaybe
                ( \(loc, rhsLoc) -> case loc of
                    EndOfReg _ Output dstEnd -> do
                      srcEnd <- rhsEndCursorReg rhsLoc
                      dstVar <- M.lookup (fromRegVarToFreeVarsTy dstEnd) freeVarToVarEnv'
                      srcVar <- M.lookup (fromRegVarToFreeVarsTy srcEnd) freeVarToVarEnv'
                      let srcTy = fmap unTy2 (M.lookup srcVar tenv')
                      case srcTy of
                            Just (CursorArrayTy sz) -> pure (dstVar, [], CursorArrayTy sz, VarE srcVar)
                            Just MutCursorTy -> pure (dstVar, [], CursorTy, Ext $ DerefMutCursor srcVar)
                            _ -> pure (dstVar, [], CursorTy, VarE srcVar)
                    _ -> Nothing
                )
                (zip locs rhsLocs)
            else []

      (bnds, m11', m22') <- dbgTrace (minChatLvl) "Print locs in cursorize Let " dbgTrace (minChatLvl) (sdoc (ty', locs, m1', m2', start_loc, start_var, useMutableCursors)) dbgTrace (minChatLvl) "End cursorize Let 2\n" case locs of
            [] -> if M.member start_loc m2'
                  -- If we have a packed type and its start location is an output mutable location.
                  -- Then, the start of the output location is where the old location points to.
                  -- The end of the location is where the output mutable location currently points to. 
                  -- To get the end we just dereference the output mutable location.
                  -- The start of the packed type is v, we get this from the start of the mutable cursor
                  then
                    do 
                    let (oldvarmut, endreg) = case M.lookup start_loc m2' of 
                                                        Nothing -> error "Expected to have the output mutable location in env!"
                                                        Just (oldvar, _oldloc, ereg, _aliases) -> (oldvar, ereg)
                    let type_l2 = getCursorizeTyFromLocVar Nothing useMutableCursors start_loc
                    new_deref <- gensym "deref"
                    case start_loc of 
                          Single{} -> do 
                                      let m1'' = updateMutableLocPtsToEnv start_loc m1' (toEndV v, Just start_loc, Nothing, S.empty) False
                                      pure ([ (fresh, [], fresh_ty, rhs'),
                                              (v, [], type_l2, VarE oldvarmut),
                                              (new_deref, [], type_l2, Ext $ DerefMutCursor (getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy start_loc))),
                                              (toEndV v, [], type_l2, VarE new_deref)
                                            ], m1'', m2')
                          SoA{} -> do 
                                   let m1'' = updateMutableLocPtsToEnv start_loc m1' (toEndV v, Just start_loc, Nothing, S.empty) False
                                   pure ([ (fresh, [], fresh_ty, rhs'),
                                           (v, [], type_l2, VarE oldvarmut),
                                           (toEndV v, [], type_l2, Ext $ InitCursor type_l2),
                                           ("_", [], ProdTy [], Ext $ MemCpy (toEndV v) (getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy start_loc)) type_l2)
                                         ], m1'', m2')
                  else if useMutableCursors
                  then
                    do
                    -- find the output mutable location that points to the start_var of the packed ty
                    let mut_loc = dbgTrace (minChatLvl) "Print in cursorizeLet: " dbgTrace (minChatLvl) (sdoc (M.toList m1')) dbgTrace (minChatLvl) "End in cursorizeLet.\n" L.foldr (\(ml, lst) res -> 
                                                            foldr (\(vv, vl, erg, _alises) res' ->       
                                                                    if vv == start_var
                                                                    then Just (ml, erg)
                                                                    else res'
                                                                  ) res lst
                                          ) Nothing (M.toList m1')
                    case mut_loc of 
                              -- Preserve the packed let binding even if we cannot
                              -- recover a mutable-location edge.
                              Nothing ->
                                let type_l2 = getCursorizeTyFromLocVar Nothing useMutableCursors start_loc
                                    start_rhs =
                                      case (type_l2, M.lookup start_var tenv) of
                                        (CursorTy, Just (MkTy2 MutCursorTy)) -> Ext $ DerefMutCursor start_var
                                        _ -> VarE start_var
                                    end_rhs =
                                      if rhsStillReturnsPackedEndpoints
                                      then mkProj 1 rhs''
                                      else start_rhs
                                 in pure ([ (fresh, [], fresh_ty, rhs')
                                          , (v, [], type_l2, start_rhs)
                                          , (toEndV v, [], type_l2, end_rhs)
                                          ], m1', m2')
                              Just (l, endreg) -> do
                                        let type_l2 = getCursorizeTyFromLocVar Nothing useMutableCursors start_loc
                                        let varName = (getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy l))
                                        new_deref <- gensym "deref"
                                        case start_loc of 
                                              Single{} -> do 
                                                           let m1'' = updateMutableLocPtsToEnv l m1' (toEndV v, Just l, Nothing, S.empty) False
                                                           pure ([ (fresh, [], fresh_ty, rhs'),
                                                              --(v, [], projTy 0 ty'', mkProj 0 rhs''),
                                                              --(toEndV v, [], projTy 1 ty'', mkProj 1 rhs'')
                                                              (v, [], getCursorizeTyFromLocVar Nothing useMutableCursors start_loc, VarE start_var), 
                                                              -- TODO: make a new name using gensym
                                                              (new_deref, [], CursorTy, Ext $ DerefMutCursor (getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy l))),
                                                              (toEndV v, [], getCursorizeTyFromLocVar Nothing useMutableCursors start_loc, VarE new_deref) 
                                                              --()
                                                            ], m1'', m2')
                                              SoA{} -> do 
                                                       let m1'' = updateMutableLocPtsToEnv l m1' (toEndV v, Just l, Nothing, S.empty) False
                                                       pure ([ (fresh, [], fresh_ty, rhs'),
                                                              --(v, [], projTy 0 ty'', mkProj 0 rhs''),
                                                              --(toEndV v, [], projTy 1 ty'', mkProj 1 rhs'')
                                                              (v, [], getCursorizeTyFromLocVar Nothing useMutableCursors start_loc, VarE start_var), 
                                                              -- TODO: make a new name using gensym
                                                              -- (new_deref, [], CursorTy, Ext $ DerefMutCursor (getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy l))),
                                                              -- (toEndV v, [], getCursorizeTyFromLocVar Nothing useMutableCursorsCall start_loc, VarE new_deref) 
                                                              --()
                                                              (toEndV v, [], type_l2, Ext $ InitCursor type_l2),
                                                              ("_", [], ProdTy [], Ext $ MemCpy (toEndV v) varName type_l2)
                                                            ], m1'', m2') 
                  else do
                    pure ([ (fresh, [], fresh_ty, rhs'),
                           (v, [], projTy 0 ty'', mkProj 0 rhs''),
                           (toEndV v, [], projTy 1 ty'', mkProj 1 rhs'')
                         ], m1', m2')
            _ -> if M.member start_loc m2'
                  -- If we have a packed type and its start location is an output mutable location.
                  -- Then, the start of the output location is where the old location points to.
                  -- The end of the location is where the output mutable location currently points to. 
                  -- To get the end we just dereference the output mutable location.
                  -- The start of the packed type is v, we get this from the start of the mutable cursor
                  then
                    do 
                    let (oldvarmut, endreg) = case M.lookup start_loc m2' of 
                                                        Nothing -> error "Expected to have the output mutable location in env!"
                                                        Just (oldvar, _oldloc, ereg, _aliases) -> (oldvar, ereg)
                    
                    let type_l2 = getCursorizeTyFromLocVar Nothing useMutableCursors start_loc
                    let varName = (getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy start_loc))
                    new_deref <- gensym "deref"
                    let (loc_bnds, m1'', m2'') = foldr (\(loc, n) (lbndsi, m1i, m2i) -> let loc_var = fromLocArgToFreeVarsTy loc
                                                                                            regVarLoc = fromJust endreg
                                                                                            varNameReg = (getVarNameFromFreeVar freeVarToVarEnv' (fromRegVarToFreeVarsTy regVarLoc))
                                                                                            varNameTy :: Ty3 = case M.lookup varNameReg tenv of 
                                                                                                                   Nothing -> CursorTy
                                                                                                                   Just ty -> case (unTy2 ty) of 
                                                                                                                                      CursorTy -> CursorTy 
                                                                                                                                      MutCursorTy -> MutCursorTy 
                                                                                            cursor_ty = cursor_ty_locs' !! n
                                                                                            loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv') of
                                                                                                         Just v -> v
                                                                                                         Nothing -> error "cursorizeLet: unexpected location variable"
                                                                                          in case loc of 
                                                                                                -- Vidush: 
                                                                                                -- TODO, i might need to implement other cases here??
                                                                                                EndOfReg r m er -> if m == Output
                                                                                                                   then case regVarLoc of
                                                                                                                       SingleR{} -> case varNameTy of 
                                                                                                                                            CursorTy -> (lbndsi ++ [(loc_to_variable, [], cursor_ty, VarE varNameReg)], m1i, m2i) 
                                                                                                                                            MutCursorTy -> (lbndsi ++ [(loc_to_variable, [], cursor_ty, Ext $ DerefMutCursor varNameReg)], m1i, m2i) 
                                                                                                                       SoARv{} ->
                                                                                                                                 let reg_ty = getCursorizeTyFromRegVar Nothing useMutableCursorsCall regVarLoc
                                                                                                                                 in (lbndsi ++ [(loc_to_variable, [], reg_ty, VarE varNameReg)], m1i, m2i)
                                                                                                                   -- We need to find output locations that belong to this region.
                                                                                                                   else if (m == OutputMutable)
                                                                                                                    -- We need to check which one is an output location
                                                                                                                    -- For the output location, we find the mutable location and update the
                                                                                                                    -- environment to point to the output mutable location.
                                                                                                                   then
                                                                                                                    let output = foldr (\locarg ret -> case locarg of 
                                                                                                                                                              EndOfReg{} -> ret
                                                                                                                                                              Loc lrem -> let 
                                                                                                                                                                            lrem_lc = lremLoc lrem
                                                                                                                                                                            lc_var = getVarNameFromFreeVar freeVarToVarEnv' (fromLocVarToFreeVarsTy lrem_lc)
                                                                                                                                                                            mut_loc_lc = findMutableLocationPointingToVar lc_var m1'
                                                                                                                                                                           in case mut_loc_lc of 
                                                                                                                                                                                      Nothing -> ret
                                                                                                                                                                                      Just l -> let mbkey = M.lookup l m1'
                                                                                                                                                                                                  in case mbkey of 
                                                                                                                                                                                                          Nothing -> ret
                                                                                                                                                                                                          Just lst -> case lst of 
                                                                                                                                                                                                                (_, _, reg, _):xs -> dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (output, loc)) dbgTrace (minChatLvl) "End printing in EndOfReg FoldrR 1.\n"  reg
                                                                                                                                                                                                                [] -> error "Expected a key in the env!"
                                                                                                                                                              _ -> ret
                                                                                                                                       ) Nothing locs
                                                                                                                     in case output of 
                                                                                                                            Nothing -> dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (output, loc, locs)) dbgTrace (minChatLvl) "End printing in EndOfReg 1.\n" (lbndsi, m1i, m2i) --error "Expected to have a mutable location!!"
                                                                                                                            Just reg -> let regName = dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (output)) dbgTrace (minChatLvl) "End printing in EndOfReg 2.\n" getVarNameFromFreeVar freeVarToVarEnv' (fromRegVarToFreeVarsTy reg)
                                                                                                                                         in (lbndsi ++ [(loc_to_variable, [], CursorTy, VarE regName)], m1i, m2i)
                                                                                                                   else if (m == Input)
                                                                                                                   then 
                                                                                                                    (lbndsi, m1i, m2i)
                                                                                                                   else if (m == InputMutable)
                                                                                                                   then
                                                                                                                     let (input, m1i', m2i') = foldr (\locarg (ret, m1ii, m2ii) -> case locarg of 
                                                                                                                                                             EndWitness lrem _ -> let mlrem = lremMode lrem 
                                                                                                                                                                                    in case mlrem of 
                                                                                                                                                                                              InputMutable -> let 
                                                                                                                                                                                                                end = lremReg lrem
                                                                                                                                                                                                                endName = getVarNameFromFreeVar freeVarToVarEnv (fromRegVarToFreeVarsTy end)
                                                                                                                                                                                                                mut_loc_lc = findMutableLocationPointingToVar endName m1'
                                                                                                                                                                                                                loc = toLocVar locarg
                                                                                                                                                                                                               in case mut_loc_lc of 
                                                                                                                                                                                                                          Nothing -> dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (end, endName, loc)) dbgTrace (minChatLvl) "End printing in EndOfReg InputMutable 11.\n" (ret, m1ii, m2ii) 
                                                                                                                                                                                                                          Just l -> let 
                                                                                                                                                                                                                                      mk = fromJust $ M.lookup l m1'
                                                                                                                                                                                                                                      m1'' = dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (end, endName, loc)) dbgTrace (minChatLvl) "End printing in EndOfReg InputMutable 12.\n" M.insert loc mk m1'
                                                                                                                                                                                                                                     in (ret, m1'', m2ii)

                                                                                                                                                                                              _ -> (ret, m1ii, m2ii)
                                                                                                                                                             _ -> (ret, m1ii, m2ii)                          
                                                                                                                                                  ) (Nothing, m1i, m2i) locs
                                                                                                                     in (lbndsi, m1i', m2i')
                                                                                                                   else (lbndsi, m1i, m2i)
                                                                                                  -- should this be empty??
                                                                                                  -- Vidush: Check this!!
                                                                                                  -- Vidush : check if the mutable loc pts to env has any mutable variable pointing to
                                                                                                  -- one of the end witnesses. 
                                                                                                EndWitness lrem lv -> let witness_loc = lremLoc lrem
                                                                                                                          witness_reg = lremReg lrem
                                                                                                                          witness_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy witness_loc)
                                                                                                                          mut_loc = findMutableLocationPointingToVar witness_var m1
                                                                                                                        in case mut_loc of
                                                                                                                                  -- return no bnds, in case we cannot find a mut_loc
                                                                                                                                  Nothing -> -- check if loc is in the same region.
                                                                                                                                             let mut_loc_in_same_reg = findMutableLocationInSameRegion witness_reg m1
                                                                                                                                              in dbgTrace (minChatLvl) "Print in Nothing case Endwitness AppE: " dbgTrace (minChatLvl) (sdoc (witness_loc, witness_var)) dbgTrace (minChatLvl) "End in Print case EndWitness Nothing AppE 1.\n" (lbndsi, m1i, m2i)
                                                                                                                                  Just l -> let 
                                                                                                                                              locs_var = dbgTrace (minChatLvl) "Print in Nothing case Endwitness AppE: " dbgTrace (minChatLvl) (sdoc (witness_loc, witness_var)) dbgTrace (minChatLvl) "End in Print case EndWitness Just case AppE 1.\n" getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lv)
                                                                                                                                              -- update the mut loc points to env to point to the correct value, in this case the end witness.
                                                                                                                                              m1i' = updateMutableLocPtsToEnv l m1i (locs_var, Just l, Nothing, S.empty) True
                                                                                                                                              mut_l_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy l)
                                                                                                                                              loc_ty = getCursorizeTyFromLocVar Nothing False l
                                                                                                                                              bnd = case l of 
                                                                                                                                                        Single{} -> [(locs_var, [], CursorTy, cursorValueFromMaybeTrackedMut m1 tenv mut_l_var)]
                                                                                                                                                        SoA{} -> [(locs_var, [], loc_ty, Ext $ InitCursor loc_ty), ("_", [], ProdTy [], Ext $ MemCpy locs_var mut_l_var loc_ty)]
                                                                                                                                             in (lbndsi ++ bnd, m1i', m2i)
                                                                                                _ -> (lbndsi, m1i, m2i)
                                                         ) ([], m1', m2') (zip locs [0 ..]) 
                    case start_loc of 
                           Single{} -> do
                                        let m1''' = updateMutableLocPtsToEnv start_loc m1'' (toEndV v, Just start_loc, Nothing, S.empty) True
                                        pure ([ (fresh, [], fresh_ty, rhs'),
                                                (v, [], type_l2, VarE oldvarmut),
                                                (new_deref, [], type_l2, Ext $ DerefMutCursor varName),
                                                (toEndV v, [], type_l2, VarE new_deref)
                                              ] ++ loc_bnds, m1''', m2'')
                           SoA{} -> do 
                                     let m1''' = updateMutableLocPtsToEnv start_loc m1'' (toEndV v, Just start_loc, Nothing, S.empty) True
                                     pure ([ (fresh, [], fresh_ty, rhs'),
                                             (v, [], type_l2, VarE oldvarmut),
                                             (toEndV v, [], type_l2, Ext $ InitCursor type_l2),
                                             ("_", [], ProdTy [], Ext $ MemCpy (toEndV v) varName type_l2)
                                             --(new_deref, [], type_l2, Ext $ DerefMutCursor varName),
                                             --(toEndV v, [], type_l2, VarE new_deref)
                                           ] ++ loc_bnds, m1''', m2'')
                 else if useMutableCursors
                 then 
                  -- find the output mutable location that points to the start_var of the packed ty
                  let mut_loc = L.foldr (\(ml, lst) res -> 
                                          foldr (\(vv, vl, erg, _aliases) res' -> 
                                                                  if vv == start_var
                                                                  then Just (ml, erg)
                                                                  else res'
                                                ) res lst 
                                          ) Nothing (M.toList m1')
                    in case mut_loc of
                            -- Same fallback as locs=[] above.
                            Nothing ->
                              let type_l2 = getCursorizeTyFromLocVar Nothing useMutableCursors start_loc
                                  start_rhs =
                                    case (type_l2, M.lookup start_var tenv) of
                                      (CursorTy, Just (MkTy2 MutCursorTy)) -> Ext $ DerefMutCursor start_var
                                      _ -> VarE start_var
                                  end_rhs =
                                    if rhsStillReturnsPackedEndpoints
                                    then mkProj 1 rhs''
                                    else start_rhs
                               in pure ([ (fresh, [], fresh_ty, rhs')
                                        , (v, [], type_l2, start_rhs)
                                        , (toEndV v, [], type_l2, end_rhs)
                                        ], m1', m2')
                  -- let nLocs = length locs
                  --     locBnds = map
                  --                 (\(loc, n) -> let loc_var = fromLocArgToFreeVarsTy loc
                  --                                   cursor_ty = cursor_ty_locs' !! n
                  --                                   loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv') of
                  --                                                         Just v -> v
                  --                                                         Nothing -> error "cursorizeLet: unexpected location variable"
                  --                                in (loc_to_variable, [], cursor_ty, mkProj n rhs'')
                  --                 ) (zip locs [0 ..])
                            Just (l, endreg) -> do 
                                      new_deref <- gensym "deref"
                                      let tylocvar = getCursorizeTyFromLocVar Nothing useMutableCursors start_loc
                                      let varName = (getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy l))
                                      let start_rhs = case M.lookup l m2' of
                                                        Just (oldvar, _oldloc, _ereg, _aliases) -> VarE oldvar
                                                        Nothing -> case (tylocvar, M.lookup start_var tenv) of
                                                          (CursorTy, Just (MkTy2 MutCursorTy)) -> Ext $ DerefMutCursor start_var
                                                          _ -> VarE start_var
                                      let (loc_bnds, m1'', m2'') = foldr (\(loc, n) (lbndsi, m1i, m2i) -> let loc_var = fromLocArgToFreeVarsTy loc
                                                                                                              location_var = toLocVar loc
                                                                                                              cursor_ty = cursor_ty_locs' !! n
                                                                                                              loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv') of
                                                                                                                                      Just v -> v
                                                                                                                                      Nothing -> error "cursorizeLet: unexpected location variable"
                                                                                                          in case loc of 
                                                                                                                  -- Vidush: 
                                                                                                                  -- TODO, i might need to implement other cases here??
                                                                                                                  EndOfReg r m er -> if m == Output
                                                                                                                                     then
                                                                                                                                      case M.lookup (fromRegVarToFreeVarsTy $ fromJust endreg) freeVarToVarEnv of
                                                                                                                                          Just endRegName ->
                                                                                                                                            case M.lookup endRegName tenv of
                                                                                                                                              Just ty -> case unTy2 ty of
                                                                                                                                                CursorArrayTy sz -> ([(loc_to_variable, [], CursorArrayTy sz, VarE endRegName)], m1i, m2i)
                                                                                                                                                MutCursorTy -> ([(loc_to_variable, [], CursorTy, Ext $ DerefMutCursor endRegName)], m1i, m2i)
                                                                                                                                                _ -> ([(loc_to_variable, [], CursorTy, VarE endRegName)], m1i, m2i)
                                                                                                                                              Nothing ->
                                                                                                                                                case r of
                                                                                                                                                  SoARv{} ->
                                                                                                                                                    let CursorArrayTy sz = getCursorizeTyFromRegVar Nothing useMutableCursorsCall r
                                                                                                                                                    in ([(loc_to_variable, [], CursorArrayTy sz, VarE endRegName)], m1i, m2i)
                                                                                                                                                  SingleR{} -> ([(loc_to_variable, [], CursorTy, VarE endRegName)], m1i, m2i)
                                                                                                                                          Nothing -> ([], m1i, m2i)
                                                                                                                                    else if (m == OutputMutable)
                                                                                                                                      -- We need to check which one is an output location
                                                                                                                                      -- For the output location, we find the mutable location and update the
                                                                                                                                      -- environment to point to the output mutable location.
                                                                                                                                    then
                                                                                                                                      let output = foldr (\locarg ret -> case locarg of 
                                                                                                                                                                                EndOfReg{} -> ret
                                                                                                                                                                                Loc lrem -> let 
                                                                                                                                                                                              lrem_lc = lremLoc lrem
                                                                                                                                                                                              lc_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lrem_lc)
                                                                                                                                                                                              mut_loc_lc = findMutableLocationPointingToVar lc_var m1'
                                                                                                                                                                                            in case mut_loc_lc of 
                                                                                                                                                                                                        Nothing -> ret
                                                                                                                                                                                                        Just l -> let mbkey = M.lookup l m1'
                                                                                                                                                                                                                    in case mbkey of 
                                                                                                                                                                                                                            Nothing -> ret
                                                                                                                                                                                                                            Just lst -> case lst of 
                                                                                                                                                                                                                                            (_, _, reg, _):xs -> dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (output, loc)) dbgTrace (minChatLvl) "End printing in EndOfReg FoldrR 2.\n"  reg
                                                                                                                                                                                                                                            [] -> error "Expected to have values for keys!"
                                                                                                                                                                                _ -> ret
                                                                                                                                                        ) Nothing locs
                                                                                                                                      in case output of
                                                                                                                                              -- dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (output, loc, locs)) dbgTrace (minChatLvl) "End printing in EndOfReg 12.\n" (lbndsi, m1i, m2i) --error "Expected to have a mutable location!!"
                                                                                                                                              Nothing -> -- find the region from the Output loc
                                                                                                                                                        let mut_loc_out = findMutableLocationPointingToVar start_var m1'
                                                                                                                                                          in case mut_loc_out of 
                                                                                                                                                                      Nothing -> dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (loc, mut_loc_out, start_var)) dbgTrace (minChatLvl) "End printing in EndOfReg 21.\n" (lbndsi, m1i, m2i)
                                                                                                                                                                      Just l -> let mbkey = M.lookup l m1' 
                                                                                                                                                                                in case mbkey of 
                                                                                                                                                                                          Nothing -> (lbndsi, m1i, m2i)
                                                                                                                                                                                          Just lst -> case (findAValidRegion lst) of
                                                                                                                                                                                                                 Nothing -> dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (loc, lst)) dbgTrace (minChatLvl) "End printing in EndOfReg Just Nothing 211.\n" (lbndsi, m1i, m2i)
                                                                                                                                                                                                                      -- Instead, we need to make the current end region point to the mutable region we are keeping track of 
                                                                                                                                                                                                                      -- dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (output)) dbgTrace (minChatLvl) "End printing in EndOfReg 22.\n"
                                                                                                                                                                                                                 Just rr -> case M.lookup (fromRegVarToFreeVarsTy rr) freeVarToVarEnv' of 
                                                                                                                                                                                                                                                                    Nothing -> case M.lookup (fromRegVarToFreeVarsTy (toEndVRegVar rr)) freeVarToVarEnv' of
                                                                                                                                                                                                                                                                                                    Nothing -> dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (loc, rr, freeVarToVarEnv')) dbgTrace (minChatLvl) "End printing in EndOfReg Just Nothing Nothing Nothing 221.\n" (lbndsi, m1i, m2i)
                                                                                                                                                                                                                                                                                                    Just rrName -> let m1i' = updateMutableLocPtsToEnv location_var m1i (rrName, Just location_var, (Just rr), S.empty) True
                                                                                                                                                                                                                                                                                                                    in dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (loc, rr, freeVarToVarEnv')) dbgTrace (minChatLvl) "End printing in EndOfReg Just Nothing Nothing Just 221.\n" (lbndsi, m1i', m2i)
                                                                                                                                                                                                                                                                    Just n -> let m1i' = dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (loc, rr)) dbgTrace (minChatLvl) "End printing in EndOfReg Just Just Just 221.\n" updateMutableLocPtsToEnv location_var m1i (n, Just location_var, (Just rr), S.empty) True
                                                                                                                                                                                                                                                                               in (lbndsi, m1i', m2i)
                                                                                                                                              Just reg -> let regName = dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (loc)) dbgTrace (minChatLvl) "End printing in EndOfReg 22.\n" getVarNameFromFreeVar freeVarToVarEnv (fromRegVarToFreeVarsTy reg)
                                                                                                                                                          in (lbndsi ++ [(loc_to_variable, [], CursorTy, VarE regName)], m1i, m2i)
                                                                                                                                    else if (m == InputMutable)
                                                                                                                                      then
                                                                                                                                        let (input, m1i', m2i') = foldr (\locarg (ret, m1ii, m2ii) -> case locarg of 
                                                                                                                                                                                EndWitness lrem _ -> let mlrem = lremMode lrem 
                                                                                                                                                                                                        in case mlrem of 
                                                                                                                                                                                                                  InputMutable -> let 
                                                                                                                                                                                                                                    reg = lremReg lrem
                                                                                                                                                                                                                                    end =  toEndVRegVar reg
                                                                                                                                                                                                                                    endName = getVarNameFromFreeVar freeVarToVarEnv (fromRegVarToFreeVarsTy end)
                                                                                                                                                                                                                                    regName = getVarNameFromFreeVar freeVarToVarEnv (fromRegVarToFreeVarsTy reg)
                                                                                                                                                                                                                                    mut_loc_lc = findMutableLocationPointingToVar regName m1'
                                                                                                                                                                                                                                    loc_endwit = toLocVar locarg
                                                                                                                                                                                                                                    loc_loc = toLocVar loc
                                                                                                                                                                                                                                    -- loc_loc_name = case loc_loc of 
                                                                                                                                                                                                                                    --                       Single r -> r
                                                                                                                                                                                                                                    --                       _ -> regName 
                                                                                                                                                                                                                                  in case mut_loc_lc of 
                                                                                                                                                                                                                                              Nothing -> let 
                                                                                                                                                                                                                                                           m1'' = dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (end, endName, loc)) dbgTrace (minChatLvl) "End printing in EndOfReg InputMutable 21.\n" updateMutableLocPtsToEnv loc_loc m1ii (endName, Just loc_loc, Just reg, S.fromList []) True
                                                                                                                                                                                                                                                          in (ret, m1'', m2ii)
                                                                                                                                                                                                                                              Just l -> let 
                                                                                                                                                                                                                                                          mk = fromJust $ M.lookup l m1'
                                                                                                                                                                                                                                                          m1'' = dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (end, endName, loc, loc_endwit)) dbgTrace (minChatLvl) "End printing in EndOfReg InputMutable 22.\n" M.insert loc_endwit mk m1ii
                                                                                                                                                                                                                                                        in (ret, m1'', m2ii)

                                                                                                                                                                                                                  _ -> (ret, m1ii, m2ii)
                                                                                                                                                                                _ -> (ret, m1ii, m2ii)                          
                                                                                                                                                                      ) (Nothing, m1i, m2i) locs
                                                                                                                                         in (lbndsi, m1i', m2i')
                                                                                                                                    else (lbndsi, m1i, m2i)
                                                                                                                  -- EndWitness lrem lvar -> 
                                                                                                                  -- should this be empty??
                                                                                                                  -- Vidush: Check this!!
                                                                                                                  -- Vidush : check if the mutable loc pts to env has any mutable variable pointing to
                                                                                                                        -- one of the end witnesses. 
                                                                                                                  EndWitness lrem lv -> let witness_loc = lremLoc lrem
                                                                                                                                            witness_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy witness_loc)
                                                                                                                                            witness_reg = lremReg lrem
                                                                                                                                            mut_loc = findMutableLocationPointingToVar witness_var m1
                                                                                                                                          in case mut_loc of
                                                                                                                                                            -- return no bnds, in case we cannot find a mut_loc
                                                                                                                                                      Nothing -> let mut_loc_in_same_reg = findMutableLocationInSameRegion witness_reg m1 
                                                                                                                                                                  in case mut_loc_in_same_reg of 
                                                                                                                                                                              Nothing -> (lbndsi, m1i, m2i)
                                                                                                                                                                              Just (_pts_to_val, mut_loc) -> let mut_loc_name = dbgTrace (minChatLvl) "Print in Nothing case Endwitness AppE: " dbgTrace (minChatLvl) (sdoc (witness_loc, witness_var, mut_loc_in_same_reg, witness_reg)) dbgTrace (minChatLvl) "End in Print case EndWitness Nothing AppE 2.\n" getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy mut_loc)
                                                                                                                                                                                                              in case mut_loc of 
                                                                                                                                                                                                                        Single{} -> let locs_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lv)
                                                                                                                                                                                                                                        bnd = [(locs_var, [], CursorTy, cursorValueFromMaybeTrackedMut m1 tenv mut_loc_name)]
                                                                                                                                                                                                                                        m1i' = updateMutableLocPtsToEnv l m1i (locs_var, Just l, Nothing, S.empty) True
                                                                                                                                                                                                                                     in (lbndsi ++ bnd, m1i', m2i)
                                                                                                                                                                                                                        SoA{} -> let locs_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lv)
                                                                                                                                                                                                                                     ty_of_cur = getCursorizeTyFromLocVar Nothing True mut_loc   
                                                                                                                                                                                                                                     bnd = [(locs_var, [], ty_of_cur, Ext $ InitCursor ty_of_cur), ("_", [], ProdTy [], Ext $ MemCpy locs_var mut_loc_name ty_of_cur)]
                                                                                                                                                                                                                                     m1i' = updateMutableLocPtsToEnv mut_loc m1i (locs_var, Just mut_loc, Nothing, S.empty) True
                                                                                                                                                                                                                                     in (lbndsi ++ bnd, m1i', m2i)
                                                                                                                                                      Just l -> case l of 
                                                                                                                                                                    Single{} -> 
                                                                                                                                                                              let 
                                                                                                                                                                                locs_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lv)
                                                                                                                                                                                m1i' = updateMutableLocPtsToEnv l m1i (locs_var, Just l, Nothing, S.empty) True
                                                                                                                                                                                mut_l_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy l)
                                                                                                                                                                                bnd = [(locs_var, [], CursorTy, cursorValueFromMaybeTrackedMut m1 tenv mut_l_var)]
                                                                                                                                                                              in dbgTrace (minChatLvl) "Print in Nothing case Endwitness AppE: " dbgTrace (minChatLvl) (sdoc (witness_loc, witness_var, m1i, l, locs_var, m1i')) dbgTrace (minChatLvl) "End in Print case Single EndWitness Just case AppE 2.\n" (lbndsi ++ bnd, m1i', m2i)
                                                                                                                                                                    SoA{} -> 
                                                                                                                                                                              let 
                                                                                                                                                                                locs_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lv)
                                                                                                                                                                                ty_of_cur = getCursorizeTyFromLocVar Nothing True l   
                                                                                                                                                                                m1i' = updateMutableLocPtsToEnv l m1i (locs_var, Just l, Nothing, S.empty) True
                                                                                                                                                                                mut_l_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy l)
                                                                                                                                                                                bnd = [(locs_var, [], ty_of_cur, Ext $ InitCursor ty_of_cur), ("_", [], ProdTy [], Ext $ MemCpy locs_var mut_l_var ty_of_cur)]
                                                                                                                                                                              in dbgTrace (minChatLvl) "Print in Nothing case Endwitness AppE: " dbgTrace (minChatLvl) (sdoc (witness_loc, witness_var, m1i, l, locs_var, m1i')) dbgTrace (minChatLvl) "End in Print case SoA EndWitness Just case AppE 2.\n" (lbndsi ++ bnd, m1i', m2i)
                                                                                                                  _ -> (lbndsi, m1i, m2i)
                                                         ) ([], m1', m2') (zip locs [0 ..])
                                      case start_loc of 
                                              Single{} -> do
                                                          let m1''' = updateMutableLocPtsToEnv l m1'' (toEndV v, Just l, Nothing, S.empty) True
                                                          let bnds' = [ (fresh, [], fresh_ty, rhs'),
                                                                        -- (v, [], projTy 0 $ projTy nLocs ty'', mkProj 0 $ mkProj nLocs rhs''),
                                                                        (v, [], tylocvar, start_rhs), 
                                                                        --(toEndV v, [], projTy 1 $ projTy nLocs ty'', mkProj 1 $ mkProj nLocs rhs'')
                                                                        (new_deref, [], CursorTy, Ext $ DerefMutCursor varName),
                                                                        (toEndV v , [], tylocvar, VarE new_deref)
                                                                        -- (toEndV v, [], tylocvar, Ext $ InitCursor tylocvar), 
                                                                        -- ("_", [], ProdTy [], Ext $ MemCpy varName (toEndV v) tylocvar) 
                                                                      ] ++ loc_bnds 
                                                          dbgTrace (minChatLvl) "Print in tail call case: " dbgTrace (minChatLvl) (sdoc (rhs, start_var)) dbgTrace (minChatLvl) "End print in tail call case cursorizeLet.\n" pure (bnds', m1''', m2'')
                                              SoA{} -> do
                                                       let m1''' = updateMutableLocPtsToEnv l m1'' (toEndV v, Just l, Nothing, S.empty) True
                                                       let bnds' = [ (fresh, [], fresh_ty, rhs'),
                                                                    -- (v, [], projTy 0 $ projTy nLocs ty'', mkProj 0 $ mkProj nLocs rhs''),
                                                                    (v, [], tylocvar, start_rhs), 
                                                                    --(toEndV v, [], projTy 1 $ projTy nLocs ty'', mkProj 1 $ mkProj nLocs rhs'')
                                                                    --(new_deref, [], CursorTy, Ext $ DerefMutCursor varName),
                                                                    --(toEndV v , [], tylocvar, VarE new_deref)
                                                                    (toEndV v, [], tylocvar, Ext $ InitCursor tylocvar), 
                                                                    ("_", [], ProdTy [], Ext $ MemCpy (toEndV v) varName tylocvar) 
                                                                  ] ++ loc_bnds
                                                       pure (bnds', m1''', m2'')
                 else 
                  -- find the output mutable location that points to the start_var of the packed ty
                  let nLocs = dbgTrace (minChatLvl) "Print in cursorizeLet Normal case: " dbgTrace (minChatLvl) (sdoc (rhs', ty'', start_var, start_loc)) dbgTrace (minChatLvl) "End in cursorize Let Normal case.\n" length locs
                      locBnds = map
                                  (\(loc, n) -> let loc_var = fromLocArgToFreeVarsTy loc
                                                    cursor_ty = cursor_ty_locs' !! n
                                                    loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv') of
                                                                          Just v -> v
                                                                          Nothing -> error "cursorizeLet: unexpected location variable"
                                                 in (loc_to_variable, [], cursor_ty, mkProj n rhs'')
                                  ) (zip locs [0 ..])
                      bnds' = [ (fresh, [], fresh_ty, rhs'),
                                (v, [], projTy 0 $ projTy nLocs ty'', mkProj 0 $ mkProj nLocs rhs''),
                                (toEndV v, [], projTy 1 $ projTy nLocs ty'', mkProj 1 $ mkProj nLocs rhs'')
                              ]
                    in pure (bnds' ++ locBnds, m1', m2') 
      case M.lookup (fromVarToFreeVarsTy (toEndV v)) denv of
        Just xs -> error $ "todo: " ++ sdoc xs
        Nothing -> return ()
      let bndNames = S.fromList [bndVar | (bndVar, _, _, _) <- bnds]
          bndsWithUnitizedEndRegs =
            bnds ++ filter (\(bndVar, _, _, _) -> not (S.member bndVar bndNames)) unitizedOutputEndRegBnds
      (bod', freeVarToVarEnv'', m1'', m2'') <- go insideTimeIt m11' m22' (M.union freeVarToVarEnv' freeVarToVarEnv) tenv' bod
      return (mkLets bndsWithUnitizedEndRegs bod', freeVarToVarEnv'', m1'', m2'')
  | hasPacked ty = do
      let cursor_ty_locs =
            map
              ( \loc ->
                  let free_var = fromLocArgToFreeVarsTy loc
                      cursorType = case free_var of
                        R r -> getCursorizeTyFromRegVar'' Nothing useMutableCursorsCall r
                        V _ -> error "cursorizeLet: did not expect a variable in locations in a LetE."
                        FL l -> getCursorizeTyFromLocVar'' Nothing useMutableCursorsCall l
                   in cursorType
              )
              locs
      let cursor_ty_locs' =
            map
              ( \loc ->
                  let free_var = fromLocArgToFreeVarsTy loc
                      cursorType :: Ty3 = case free_var of
                        R r -> getCursorizeTyFromRegVar'' Nothing useMutableCursorsCall r
                        V _ -> error "cursorizeLet: did not expect a variable in locations in a LetE."
                        FL l -> getCursorizeTyFromLocVar'' Nothing useMutableCursorsCall l
                   in cursorType
              )
              locs
      (_rhs, freeVarToVarEnv', m1', m2') <- cursorizePackedExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv rhs
      rhs' <- fromDi <$> return _rhs 
      fresh <- gensym "tup_haspacked"
      let useMutableForPackedRhs =
            case rhs of
              AppE fn _ rhsLocs _ ->
                case M.lookup fn fundefs of
                  Just g ->
                    let fnTy = funTy g
                        isFunctionRec = case funRec (funMeta g) of
                                          TailRec -> True
                                          Rec -> True
                                          _ -> False
                        calleeHasPackedInput = any (hasPacked . unTy2) (arrIns fnTy)
                        calleeHasPackedOutput = hasPacked (unTy2 (arrOut fnTy))
                        numCallRegs = length (outRegVars fnTy) + length (L2.outRegVarsMutable fnTy) + length (inRegVars fnTy)
                        calleeHasPackedLocations = numCallRegs > 0 || not (null (locVars fnTy)) || not (null (locRets fnTy)) || not (null rhsLocs)
                        calleeHasMutableLocations =
                          not (null (L2.outRegVarsMutable fnTy))
                          || any (isMutModality . lrmMode) (L2.inRegVars' fnTy ++ locVars fnTy)
                          || any (\(EndOf lrm) -> isMutModality (lrmMode lrm)) (locRets fnTy)
                     in isFunctionRec && (useMutableCursorsCall || calleeHasMutableLocations)
                  Nothing -> False
              _ -> False
          ty' = case locs of
            [] -> cursorizeTy freeVarToVarEnv' m1' m2' useMutableCursorsCall Nothing ty
            _ | useMutableForPackedRhs -> cursorizeTy freeVarToVarEnv' m1' m2' useMutableCursorsCall Nothing ty
            _ -> ProdTy (cursor_ty_locs ++ [cursorizeTy freeVarToVarEnv' m1' m2' useMutableCursorsCall Nothing ty])
          ty'' = stripTyLocs ty'
          tenv' =
            M.union
              (M.insert v (MkTy2 ty) tenv)
              ( M.fromList $
                  map
                    ( \loc ->
                        let loc_var = fromLocArgToFreeVarsTy loc
                            loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv') of
                              Just v -> v
                              Nothing -> error "cursorizeLet: unexpected location variable"
                            cursorType = cursor_ty_locs !! (fromJust $ L.elemIndex loc locs)
                         in (loc_to_variable, MkTy2 cursorType)
                    )
                    locs
              )
      case locs of
        [] -> do 
          (bod', freeVarToVarEnv'', m1'', m2'') <- go insideTimeIt m1' m2' (M.union freeVarToVarEnv' freeVarToVarEnv) tenv' bod
          return (LetE (v, [], ty'', rhs') bod', freeVarToVarEnv'', m1'', m2'') 
        _ -> do
          let tenv'' =
                M.union tenv' $
                  M.fromList $
                    map
                      ( \loc ->
                          let loc_var = fromLocArgToFreeVarsTy loc
                              loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv') of
                                Just v' -> v'
                                Nothing -> error "cursorizeLet: unexpected location variable"
                              cursorType = cursor_ty_locs !! (fromJust $ L.elemIndex loc locs)
                           in (loc_to_variable, MkTy2 cursorType)
                      )
                      locs

              mutableLocBnds =
                case rhs of
                  AppE _ _ rhsLocs _ ->
                    concatMap
                      ( \(loc, rhsLoc, n) ->
                          case loc of
                            EndOfReg{} ->
                              let loc_var = fromLocArgToFreeVarsTy loc
                                  loc_to_variable = case M.lookup loc_var freeVarToVarEnv' of
                                    Just v' -> v'
                                    Nothing -> error "cursorizeLet: unexpected location variable"
                                  rhs_var = getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy rhsLoc)
                                  cursorType = cursor_ty_locs' !! n
                                  cursorTypeForLoc = case loc of
                                    EndOfReg r _ _ -> case r of
                                      SoARv{} -> getCursorizeTyFromRegVar Nothing useMutableCursorsCall r
                                      SingleR{} -> cursorType
                                  rhs_exp = case loc of
                                    EndOfReg SoARv{} _ _ -> VarE rhs_var
                                    _ -> case M.lookup rhs_var tenv of
                                      Just rhs_ty ->
                                        case unTy2 rhs_ty of
                                          MutCursorTy -> Ext $ DerefMutCursor rhs_var
                                          _ -> VarE rhs_var
                                      Nothing -> VarE rhs_var
                               in [(loc_to_variable, [], cursorTypeForLoc, rhs_exp)]
                            _ -> []
                      )
                      (zip3 locs rhsLocs [0..])
                  _ -> []
              bnds =
                if useMutableForPackedRhs
                then [(v, [], ty'', rhs')] ++ mutableLocBnds
                else
                  [(fresh, [], ty'', rhs')]
                    ++ map
                      ( \(loc, n) ->
                          let loc_var = fromLocArgToFreeVarsTy loc
                              loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv') of
                                Just v' -> v'
                                Nothing -> error "cursorizeLet: unexpected location variable"
                              cursorType = cursor_ty_locs' !! n
                           in (loc_to_variable, [], cursorType, ProjE n (VarE fresh))
                      )
                      (zip locs [0 ..])
                    ++ [(v, [], projTy (length locs) ty'', ProjE (length locs) (VarE fresh))]
          (bod', freeVarToVarEnv'', m1', m2') <- go insideTimeIt m1 m2 (M.union freeVarToVarEnv' freeVarToVarEnv) tenv'' bod
          return (mkLets bnds bod', freeVarToVarEnv'', m1', m2') 

  {-

  This was a scalar binding before, but now has been transformed to
  also return an end_read cursor. So the type of the binding now
  becomes:

      ProdTy [CursorTy, old_ty]

  Also, the binding itself now changes to:

      end_read -> ProjE 0 RHS'
      v        -> ProjE 1 RHS'

  `rightmost` is an example of a program that does this.

  -}

  | otherwise = do
      let rhsCallInfo =
            case rhs of
              AppE fn _ rhsLocs _ ->
                case M.lookup fn fundefs of
                  Nothing -> error $ "cursorizeLet: unknown function in AppE: " ++ sdoc fn
                  Just g ->
                    let fnTy = funTy g
                        fmeta = funMeta g
                        isFunctionRec = case funRec fmeta of
                                          TailRec -> True
                                          Rec -> True
                                          _ -> False
                        calleeHasPackedInput = any (hasPacked . unTy2) (arrIns fnTy)
                        calleeHasPackedOutput = hasPacked (unTy2 (arrOut fnTy))
                        numRegs = length (outRegVars fnTy) + length (L2.outRegVarsMutable fnTy) + length (inRegVars fnTy)
                        calleeHasPackedLocations = numRegs > 0 || not (null (locVars fnTy)) || not (null (locRets fnTy)) || not (null rhsLocs)
                        calleeHasMutableLocations =
                          not (null (L2.outRegVarsMutable fnTy))
                          || any (isMutModality . lrmMode) (L2.inRegVars' fnTy ++ locVars fnTy)
                          || any (\(EndOf lrm) -> isMutModality (lrmMode lrm)) (locRets fnTy)
                        useMutForCall = isFunctionRec && (useMutableCursorsCall || calleeHasMutableLocations)
                        numOutCursors = numRegs + length (locRets fnTy)
                     in (useMutForCall, numOutCursors, calleeHasPackedOutput)
              _ -> (useMutableCursorsCall, 0, False)
      let (useMutableForRhs, rhsNumOutCursors, rhsHasPackedOutput) = rhsCallInfo
      let cursor_ty_locs =
            map
              ( \loc ->
                  let free_var = fromLocArgToFreeVarsTy loc
                      cursorType = case free_var of
                        R r -> getCursorizeTyFromRegVar'' Nothing useMutableForRhs r
                        V _ -> error "cursorizeLet: did not expect a variable in locations in a LetE."
                        FL l -> getCursorizeTyFromLocVar'' Nothing useMutableForRhs l
                   in cursorType
              )
              locs
      let cursor_ty_locs' =
            map
              ( \loc ->
                  let free_var = fromLocArgToFreeVarsTy loc
                      cursorType :: Ty3 = case free_var of
                        R r -> getCursorizeTyFromRegVar'' Nothing useMutableForRhs r
                        V _ -> error "cursorizeLet: did not expect a variable in locations in a LetE."
                        FL l -> getCursorizeTyFromLocVar'' Nothing useMutableForRhs l
                   in cursorType
              )
              locs
      (rhs', freeVarToVarEnv', m1', m2') <- cursorizeExp m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt freeVarToVarEnv lenv ddfs fundefs denv tenv senv rhs
      let scalarCallProjIx =
            case rhs of
              AppE {} ->
                if (not useMutableForRhs) && (not rhsHasPackedOutput) && (rhsNumOutCursors > 0)
                  then Just rhsNumOutCursors
                  else Nothing
              _ -> Nothing
      case locs of
        [] -> do 
          let rhs_for_bind = case scalarCallProjIx of
                               Just ix -> ProjE ix rhs'
                               Nothing -> rhs'
          (bod', freeVarToVarEnv'', m1'', m2'') <- go insideTimeIt m1' m2' (M.union freeVarToVarEnv' freeVarToVarEnv) (M.insert v (MkTy2 ty) tenv) bod
          return (LetE (v, [], curDict $ stripTyLocs ty, rhs_for_bind) bod', freeVarToVarEnv'', m1'', m2'')
        _ -> do
          fresh <- gensym "tup_scalar"
          let rhs'' = VarE fresh
              -- Vidush: TODO rename useMutableCursorsCall to something like useMutableCursors... 
              ty' = if useMutableForRhs
                    then cursorizeTy freeVarToVarEnv' m1' m2' useMutableForRhs Nothing ty
                    else ProdTy (cursor_ty_locs ++ [cursorizeTy freeVarToVarEnv' m1 m2 useMutableForRhs Nothing ty])
              -- We cannot resuse ty' here because TyEnv Ty2 and expresssions are
              -- tagged with different
              ty'' = stripTyLocs ty'
              tenv' =
                M.union (M.insert v (MkTy2 ty) tenv) $
                  M.fromList $
                    map
                      ( \loc ->
                          let loc_var = fromLocArgToFreeVarsTy loc
                              loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv') of
                                Just v -> v
                                Nothing -> error "cursorizeLet: unexpected location variable"
                              cursorType = cursor_ty_locs !! (fromJust $ L.elemIndex loc locs)
                           in (loc_to_variable, MkTy2 cursorType)
                      )
                      locs
          let fallbackScalarLocBnds =
                case rhs of
                  AppE _ _ rhsLocs _ | useMutableForRhs ->
                    Mb.mapMaybe
                      ( \(loc, rhsLoc, n) ->
                          let loc_var = fromLocArgToFreeVarsTy loc
                              loc_to_variable = case M.lookup loc_var freeVarToVarEnv' of
                                Just v' -> v'
                                Nothing -> error "cursorizeLet: unexpected location variable"
                              rhs_var = getVarNameFromFreeVar freeVarToVarEnv' (fromLocArgToFreeVarsTy rhsLoc)
                              cursorType = cursor_ty_locs' !! n
                              cursorTypeForLoc = case loc of
                                EndOfReg r _ _ -> case r of
                                  SoARv{} -> getCursorizeTyFromRegVar Nothing useMutableCursorsCall r
                                  SingleR{} -> cursorType
                                _ -> cursorType
                              rhs_exp = case loc of
                                EndOfReg SoARv{} _ _ -> VarE rhs_var
                                _ -> case M.lookup rhs_var tenv of
                                  Just rhs_ty -> case unTy2 rhs_ty of
                                    MutCursorTy -> Ext $ DerefMutCursor rhs_var
                                    _ -> VarE rhs_var
                                  Nothing -> VarE rhs_var
                           in case cursorTypeForLoc of
                                CursorArrayTy{} -> Nothing
                                _ -> Just (loc_to_variable, [], cursorTypeForLoc, rhs_exp)
                      )
                      (zip3 locs rhsLocs [0..])
                  _ -> []
          (bnds, m1b, m2b) <- if useMutableForRhs
                              then do
                                   let (loc_bnds, m1'', m2'') = foldr (\(loc, n) (lbndsi, m1i, m2i) -> let loc_var = fromLocArgToFreeVarsTy loc
                                                                                                           location_var = toLocVar loc
                                                                                                           cursor_ty = cursor_ty_locs' !! n
                                                                                                           loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv') of
                                                                                                                                      Just v -> v
                                                                                                                                      Nothing -> error "cursorizeLet: unexpected location variable"
                                                                                                          in case loc of
                                                                                                                  -- Vidush: 
                                                                                                                  -- TODO, i might need to implement other cases here??
                                                                                                                  EndOfReg r m er -> 
                                                                                                                                    -- if m == Output
                                                                                                                                    -- then ([(loc_to_variable, [], CursorTy, Ext $ DerefMutCursor (getVarNameFromFreeVar freeVarToVarEnv (fromRegVarToFreeVarsTy $ fromJust endreg)))], m1i, m2i)
                                                                                                                                    -- else if (m == OutputMutable)
                                                                                                                                    --   -- We need to check which one is an output location
                                                                                                                                    --   -- For the output location, we find the mutable location and update the
                                                                                                                                    --   -- environment to point to the output mutable location.
                                                                                                                                    -- then
                                                                                                                                    --   let output = foldr (\locarg ret -> case locarg of
                                                                                                                                    --                                             EndOfReg{} -> ret
                                                                                                                                    --                                             Loc lrem -> let
                                                                                                                                    --                                                           lrem_lc = lremLoc lrem
                                                                                                                                    --                                                           lc_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lrem_lc)
                                                                                                                                    --                                                           mut_loc_lc = findMutableLocationPointingToVar lc_var m1'
                                                                                                                                    --                                                         in case mut_loc_lc of
                                                                                                                                    --                                                                     Nothing -> ret
                                                                                                                                    --                                                                     Just l -> let mbkey = M.lookup l m1'
                                                                                                                                    --                                                                                 in case mbkey of
                                                                                                                                    --                                                                                         Nothing -> ret
                                                                                                                                    --                                                                                         Just (_, _, reg, _) -> dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (output, loc)) dbgTrace (minChatLvl) "End printing in EndOfReg FoldrR 2.\n"  reg
                                                                                                                                    --                                             _ -> ret
                                                                                                                                    --                     ) Nothing locs
                                                                                                                                    --   in case output of
                                                                                                                                    --           -- dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (output, loc, locs)) dbgTrace (minChatLvl) "End printing in EndOfReg 12.\n" (lbndsi, m1i, m2i) --error "Expected to have a mutable location!!"
                                                                                                                                    --           Nothing -> -- find the region from the Output loc
                                                                                                                                    --                     let mut_loc_out = findMutableLocationPointingToVar start_var m1'
                                                                                                                                    --                       in case mut_loc_out of
                                                                                                                                    --                                   Nothing -> dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (loc, mut_loc_out, start_var)) dbgTrace (minChatLvl) "End printing in EndOfReg 21.\n" (lbndsi, m1i, m2i)
                                                                                                                                    --                                   Just l -> let mbkey = M.lookup l m1'
                                                                                                                                    --                                             in case mbkey of
                                                                                                                                    --                                                       Nothing -> (lbndsi, m1i, m2i)
                                                                                                                                    --                                                       Just (_, _, reg, _) -> case reg of
                                                                                                                                    --                                                                                   Nothing -> dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (loc)) dbgTrace (minChatLvl) "End printing in EndOfReg Just Nothing 211.\n" (lbndsi, m1i, m2i)
                                                                                                                                    --                                                                                   -- Instead, we need to make the current end region point to the mutable region we are keeping track of 
                                                                                                                                    --                                                                                   -- dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (output)) dbgTrace (minChatLvl) "End printing in EndOfReg 22.\n"
                                                                                                                                    --                                                                                   Just rr -> case M.lookup (fromRegVarToFreeVarsTy rr) freeVarToVarEnv' of
                                                                                                                                    --                                                                                                                                 Nothing -> case M.lookup (fromRegVarToFreeVarsTy (toEndVRegVar rr)) freeVarToVarEnv' of
                                                                                                                                    --                                                                                                                                                                 Nothing -> dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (loc, rr, freeVarToVarEnv')) dbgTrace (minChatLvl) "End printing in EndOfReg Just Nothing Nothing Nothing 221.\n" (lbndsi, m1i, m2i)
                                                                                                                                    --                                                                                                                                                                 Just rrName -> let m1i' = M.insert location_var (rrName, Just location_var, reg, S.empty) m1i
                                                                                                                                    --                                                                                                                                                                                 in dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (loc, rr, freeVarToVarEnv')) dbgTrace (minChatLvl) "End printing in EndOfReg Just Nothing Nothing Just 221.\n" (lbndsi, m1i', m2i)
                                                                                                                                    --                                                                                                                                 Just n -> let m1i' = dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (loc, rr)) dbgTrace (minChatLvl) "End printing in EndOfReg Just Just Just 221.\n" M.insert location_var (n, Just location_var, reg, S.empty) m1i
                                                                                                                                    --                                                                                                                                            in (lbndsi, m1i', m2i)
                                                                                                                                    --           Just reg -> let regName = dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (loc)) dbgTrace (minChatLvl) "End printing in EndOfReg 22.\n" getVarNameFromFreeVar freeVarToVarEnv (fromRegVarToFreeVarsTy reg)
                                                                                                                                    --                       in (lbndsi ++ [(loc_to_variable, [], CursorTy, VarE regName)], m1i, m2i)
                                                                                                                                    if m == Output
                                                                                                                                      then
                                                                                                                                        case M.lookup (fromRegVarToFreeVarsTy er) freeVarToVarEnv' of
                                                                                                                                          Just endRegName ->
                                                                                                                                            case M.lookup endRegName tenv' of
                                                                                                                                              Just ty -> case unTy2 ty of
                                                                                                                                                CursorArrayTy sz -> (lbndsi ++ [(loc_to_variable, [], CursorArrayTy sz, VarE endRegName)], m1i, m2i)
                                                                                                                                                MutCursorTy -> (lbndsi ++ [(loc_to_variable, [], CursorTy, Ext $ DerefMutCursor endRegName)], m1i, m2i)
                                                                                                                                                _ -> (lbndsi ++ [(loc_to_variable, [], CursorTy, VarE endRegName)], m1i, m2i)
                                                                                                                                              Nothing ->
                                                                                                                                                case r of
                                                                                                                                                  SoARv{} ->
                                                                                                                                                    let CursorArrayTy sz = getCursorizeTyFromRegVar Nothing useMutableCursorsCall r
                                                                                                                                                    in (lbndsi ++ [(loc_to_variable, [], CursorArrayTy sz, VarE endRegName)], m1i, m2i)
                                                                                                                                                  SingleR{} -> (lbndsi ++ [(loc_to_variable, [], CursorTy, VarE endRegName)], m1i, m2i)
                                                                                                                                          Nothing -> (lbndsi, m1i, m2i)
                                                                                                                                      else if m == InputMutable
                                                                                                                                      then
                                                                                                                                        let (input, m1i', m2i') = foldr (\locarg (ret, m1ii, m2ii) -> case locarg of
                                                                                                                                                                                EndWitness lrem _ -> let mlrem = lremMode lrem
                                                                                                                                                                                                        in case mlrem of
                                                                                                                                                                                                                  InputMutable -> let
                                                                                                                                                                                                                                    reg = lremReg lrem
                                                                                                                                                                                                                                    end =  toEndVRegVar reg
                                                                                                                                                                                                                                    endName = getVarNameFromFreeVar freeVarToVarEnv (fromRegVarToFreeVarsTy end)
                                                                                                                                                                                                                                    regName = getVarNameFromFreeVar freeVarToVarEnv (fromRegVarToFreeVarsTy reg)
                                                                                                                                                                                                                                    mut_loc_lc = findMutableLocationPointingToVar regName m1'
                                                                                                                                                                                                                                    loc_endwit = toLocVar locarg
                                                                                                                                                                                                                                    loc_loc = toLocVar loc
                                                                                                                                                                                                                                    -- loc_loc_name = case loc_loc of 
                                                                                                                                                                                                                                    --                       Single r -> r
                                                                                                                                                                                                                                    --                       _ -> regName 
                                                                                                                                                                                                                                  in case mut_loc_lc of
                                                                                                                                                                                                                                              Nothing -> let
                                                                                                                                                                                                                                                           m1'' = dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (end, endName, loc)) dbgTrace (minChatLvl) "End printing in EndOfReg InputMutable 21.\n" updateMutableLocPtsToEnv loc_loc m1ii (endName, Just loc_loc, Just reg, S.fromList []) False
                                                                                                                                                                                                                                                          in (ret, m1'', m2ii)
                                                                                                                                                                                                                                              Just l -> let
                                                                                                                                                                                                                                                          mk = fromJust $ M.lookup l m1'
                                                                                                                                                                                                                                                          m1'' = dbgTrace (minChatLvl) "Print in EndOfReg: " dbgTrace (minChatLvl) (sdoc (end, endName, loc, loc_endwit)) dbgTrace (minChatLvl) "End printing in EndOfReg InputMutable 22.\n" M.insert loc_endwit mk m1ii
                                                                                                                                                                                                                                                        in (ret, m1'', m2ii)

                                                                                                                                                                                                                  _ -> (ret, m1ii, m2ii)
                                                                                                                                                                                _ -> (ret, m1ii, m2ii)
                                                                                                                                                                      ) (Nothing, m1i, m2i) locs
                                                                                                                                         in (lbndsi, m1i', m2i')
                                                                                                                                    else (lbndsi, m1i, m2i)
                                                                                                                  -- EndWitness lrem lvar -> 
                                                                                                                  -- should this be empty??
                                                                                                                  -- Vidush: Check this!!
                                                                                                                  -- Vidush : check if the mutable loc pts to env has any mutable variable pointing to
                                                                                                                        -- one of the end witnesses. 
                                                                                                                  EndWitness lrem lv -> let witness_loc = lremLoc lrem
                                                                                                                                            witness_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy witness_loc)
                                                                                                                                            witness_reg = lremReg lrem
                                                                                                                                            mut_loc = findMutableLocationPointingToVar witness_var m1
                                                                                                                                          in case mut_loc of
                                                                                                                                                            -- return no bnds, in case we cannot find a mut_loc
                                                                                                                                                      Nothing -> let mut_loc_in_same_reg = findMutableLocationInSameRegion witness_reg m1
                                                                                                                                                                  in case mut_loc_in_same_reg of
                                                                                                                                                                              Nothing -> (lbndsi, m1i, m2i)
                                                                                                                                                                              Just (_pts_to_val, mut_loc) -> let mut_loc_name = dbgTrace (minChatLvl) "Print in Nothing case Endwitness AppE: " dbgTrace (minChatLvl) (sdoc (witness_loc, witness_var, mut_loc_in_same_reg, witness_reg)) dbgTrace (minChatLvl) "End in Print case EndWitness Nothing AppE 2.\n" getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy mut_loc)
                                                                                                                                                                                                              in case mut_loc of
                                                                                                                                                                                                                        Single{} -> let locs_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lv)
                                                                                                                                                                                                                                        bnd = [(locs_var, [], CursorTy, cursorValueFromMaybeTrackedMut m1 tenv mut_loc_name)]
                                                                                                                                                                                                                                        m1i' = updateMutableLocPtsToEnv mut_loc m1i (locs_var, Just mut_loc, Nothing, S.empty) True
                                                                                                                                                                                                                                     in (lbndsi ++ bnd, m1i', m2i)
                                                                                                                                                                                                                        SoA{} -> let locs_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lv)
                                                                                                                                                                                                                                     ty_of_cur = getCursorizeTyFromLocVar Nothing True mut_loc
                                                                                                                                                                                                                                     bnd = [(locs_var, [], ty_of_cur, Ext $ InitCursor ty_of_cur), ("_", [], ProdTy [], Ext $ MemCpy locs_var mut_loc_name ty_of_cur)]
                                                                                                                                                                                                                                     m1i' = updateMutableLocPtsToEnv mut_loc m1i (locs_var, Just mut_loc, Nothing, S.empty) True
                                                                                                                                                                                                                                     in (lbndsi ++ bnd, m1i', m2i)
                                                                                                                                                      Just l -> case l of
                                                                                                                                                                    Single{} ->
                                                                                                                                                                              let
                                                                                                                                                                                locs_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lv)
                                                                                                                                                                                m1i' = updateMutableLocPtsToEnv l m1i (locs_var, Just l, Nothing, S.empty) True
                                                                                                                                                                                mut_l_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy l)
                                                                                                                                                                                bnd = [(locs_var, [], CursorTy, cursorValueFromMaybeTrackedMut m1 tenv mut_l_var)]
                                                                                                                                                                              in dbgTrace (minChatLvl) "Print in Nothing case Endwitness AppE: " dbgTrace (minChatLvl) (sdoc (witness_loc, witness_var, m1i, l, locs_var, m1i')) dbgTrace (minChatLvl) "End in Print case Single EndWitness Just case AppE 2.\n" (lbndsi ++ bnd, m1i', m2i)
                                                                                                                                                                    SoA{} ->
                                                                                                                                                                              let
                                                                                                                                                                                locs_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy lv)
                                                                                                                                                                                ty_of_cur = getCursorizeTyFromLocVar Nothing True l
                                                                                                                                                                                m1i' = updateMutableLocPtsToEnv l m1i (locs_var, Just l, Nothing, S.empty) True
                                                                                                                                                                                mut_l_var = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy l)
                                                                                                                                                                                bnd = [(locs_var, [], ty_of_cur, Ext $ InitCursor ty_of_cur), ("_", [], ProdTy [], Ext $ MemCpy locs_var mut_l_var ty_of_cur)]
                                                                                                                                                                              in dbgTrace (minChatLvl) "Print in Nothing case Endwitness AppE: " dbgTrace (minChatLvl) (sdoc (witness_loc, witness_var, m1i, l, locs_var, m1i')) dbgTrace (minChatLvl) "End in Print case SoA EndWitness Just case AppE 2.\n" (lbndsi ++ bnd, m1i', m2i)
                                                                                                                  _ -> (lbndsi, m1i, m2i)
                                                         ) ([], m1', m2') (zip locs [0 ..])
                                   return ([(v, [], ty'', mutableLocLetPayload (MkTy2 ty) rhs')] ++ fallbackScalarLocBnds ++ loc_bnds
                                     -- Vidush: TODO, we still need to handle the locs. 
                                     -- Instead of getting them from the projection, we need to dereference 
                                     -- the output mutable locations and regions in order to get them.
                                     -- ++ map
                                     --   ( \(loc, n) ->
                                     --       let loc_var = fromLocArgToFreeVarsTy loc
                                     --           loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv') of
                                     --             Just v -> v
                                     --             Nothing -> error "cursorizeLet: unexpected location variable"
                                     --           cursorType = cursor_ty_locs' !! n
                                     --       in (loc_to_variable, [], cursorType, ProjE n rhs'')
                                     --   )
                                     --   (zip locs [0 ..])
                                     -- ++ [(v, [], projTy (length locs) ty'', ProjE (length locs) rhs'')]
                                      , m1'', m2'')
                                 else return ([(fresh, [], ty'', rhs')]
                                      ++ map
                                        ( \(loc, n) ->
                                            let loc_var = fromLocArgToFreeVarsTy loc
                                                loc_to_variable = case (M.lookup (loc_var) freeVarToVarEnv') of
                                                  Just v -> v
                                                  Nothing -> error "cursorizeLet: unexpected location variable"
                                                cursorType = cursor_ty_locs' !! n
                                            in (loc_to_variable, [], cursorType, ProjE n rhs'')
                                        )
                                        (zip locs [0 ..])
                                      ++ [(v, [], projTy (length locs) ty'', ProjE (length locs) rhs'')]
                                      , m1', m2')
          (bod', freeVarToVarEnv'', m1b', m2b') <- go insideTimeIt m1b m2b (M.union freeVarToVarEnv' freeVarToVarEnv) tenv' bod
          return (mkLets bnds bod', freeVarToVarEnv'', m1b', m2b')
  where
    go intime m1g m2g fenv t x =
      if isPackedContext
        then
          do 
            (x', freeVarToVarEnv', m1g', m2g') <- cursorizePackedExp m1g m2g useMutableCursorsCall emitScalarCountBumps intime fenv lenv ddfs fundefs denv t senv x
            return (fromDi x', freeVarToVarEnv', m1g', m2g') 
        else cursorizeExp m1g m2g useMutableCursorsCall emitScalarCountBumps intime fenv lenv ddfs fundefs denv t senv x

{-

Unpacking constructors
~~~~~~~~~~~~~~~~~~~~~~

(1) Take a cursor pointing to the start of the tag, and advance it by 1 byte.
(2) If this DataCon has random access nodes, unpack those.
(3) If the first bound varaible is a scalar (IntTy), read it using the newly
returned cursor. Otherwise, just process the body. it'll have the correct
instructions to process other bound locations

Consider an example of unpacking of a Node^ pattern:

    (Node^ [(ind_y3, loc_ind_y3), (n1, loc_n1) , (x2 , loc_x2), (y3 , loc_y3)]
      BODY)

..TODO..

-}
unpackDataCon ::
  S.Set (DataCon, Int) ->
  MutableLocPtsToEnv -> 
  MutableLocOldValueEnv ->
  Bool ->
  Bool ->
  Bool -> 
  Var ->
  M.Map FreeVarsTy Var ->
  M.Map Var (Maybe LocVar) ->
  DDefs Ty2 ->
  FunDefs2 ->
  DepEnv ->
  TyEnv Var Ty2 ->
  SyncEnv ->
  Bool ->
  Var ->
  (DataCon, [(Var, LocArg)], Exp2) ->
  PassM (DataCon, [t], Exp3)
unpackDataCon aliveBuffers m1 m2 useMutableCursorsCall emitScalarCountBumps insideTimeIt dcon_var freeVarToVarEnv lenv ddfs fundefs denv1 tenv1 senv isPacked scrtCur (dcon, vlocs1, rhs) = do
  field_cur <- gensym "field_cur"
  let ty_of_scrut = case (M.lookup scrtCur tenv1) of
        Just (MkTy2 ty) -> ty
        Nothing -> error "unpackDataCon: unexpected location variable"
  case ty_of_scrut of
    CursorTy -> do
      let mut_loc = findMutableLocationPointingToVar scrtCur m1
      (m1', bump_bnds) <- case mut_loc of
            Nothing -> dbgTrace (minChatLvl) "Print in unpackDataCon CursorTy: " dbgTrace (minChatLvl) (sdoc (mut_loc, scrtCur)) dbgTrace (minChatLvl) "End print in unpackDataCon CursorTy\n." return (m1, [])
            Just l -> do
                      let m1inner = updateMutableLocPtsToEnv l m1 (field_cur, mut_loc, Nothing, S.empty) False
                      void <- gensym "void"
                      let lname = getVarNameFromFreeVar freeVarToVarEnv (fromLocVarToFreeVarsTy l)
                      let bmp = [(void, [], ProdTy [], Ext $ BumpCursorMutable lname (LitE 1))]
                      dbgTrace (minChatLvl) "Print in unpackDataCon CursorTy: " dbgTrace (minChatLvl) (sdoc (mut_loc, scrtCur)) dbgTrace (minChatLvl) "End print in unpackDataCon CursorTy 2\n." return (m1inner, bmp)
      -- (m1', m2')
      dbgTrace (minChatLvl) "Print scrutCur " dbgTrace (minChatLvl) (sdoc (scrtCur, ty_of_scrut, field_cur)) dbgTrace (minChatLvl) "End print scrutCur 1.\n" (dcon,[],)
        -- Advance the cursor by 1 byte so that it points to the first field
        <$> mkLets ([(field_cur, [], CursorTy, Ext $ AddCursor scrtCur (LitE 1))] ++ bump_bnds)
        <$> ( if isAbsRANDataCon dcon
                then unpackWithAbsRAN tenv1 aliveBuffers m1' m2 (AoSWin field_cur) freeVarToVarEnv
                else
                  if isRelRANDataCon dcon
                    then unpackWithRelRAN field_cur
                    else unpackRegularDataCon tenv1 aliveBuffers m1' m2 (AoSWin field_cur) freeVarToVarEnv
            )
    -- MutCursorTy -> do
    --   field_cur <- gensym "field_cur_mut"
    --   -- Vidush: We need to find the output mut location which points to this value
    --   -- (scrutCurVal, m2') <-
    --   let mutLoc = findMutableLocationPointingToVar scrtCur m1
    --   case mutLoc of 
    --         Nothing -> error "Expected to have get corresponding mutable location for scrutinee value!\n"
    --         Just outmutloc -> do
    --                           deref_val <- gensym "deref_mut_cur"
    --                           let deref_mut_cur = [(deref_val, [], CursorTy, Ext $ DerefMutCursor )]
    --   dbgTrace (minChatLvl) "Print scrutCur MutCursor Case: " dbgTrace (minChatLvl) (sdoc (scrtCur, ty_of_scrut, field_cur, mutLoc)) dbgTrace (minChatLvl) "End print scrutCur mutcur 1.\n" (dcon,[],)
    --     -- Advance the cursor by 1 byte so that it points to the first field
    --     <$> mkLets [(field_cur, [], CursorTy, Ext $ AddCursor scrtCur (LitE 1))]
    --     <$> ( if isAbsRANDataCon dcon
    --             then unpackWithAbsRAN (AoSWin field_cur) freeVarToVarEnv
    --             else
    --               if isRelRANDataCon dcon
    --                 then unpackWithRelRAN field_cur
    --                 else unpackRegularDataCon m1 m2 (AoSWin field_cur) freeVarToVarEnv
    --         )
    CursorArrayTy size -> do
      -- dcon_var <- gensym "dcon"
      let first_var = dbgTrace (minChatLvl) "Print scrutCur " dbgTrace (minChatLvl) (sdoc (scrtCur, ty_of_scrut, field_cur)) dbgTrace (minChatLvl) "End print scrutCur 2.\n" field_cur
      let scrut_loc = case (M.lookup scrtCur lenv) of
            Just loc -> case loc of
              Just l -> case l of
                Single _ -> error "unpackDataCon: Did not expect a single location for a cursor array!"
                SoA _ _ -> l
              Nothing -> error "unpackDataCon: Did not find a location for scrutinee!"
            Nothing -> error "unpackDataCon: Did not find a location for scrutinee!"

      -- let dcon_let = [(dcon_var, [], CursorTy, Ext $ IndexCursorArray scrtCur 0)]
      (field_lets, field_v_lst, freeVarToVarEnv', m1', m2', tenv1') <-
        dbgTrace
          (minChatLvl)
          "Print scrut_loc "
          dbgTrace
          (minChatLvl)
          (sdoc ((dcon, scrut_loc)))
          dbgTrace
          (minChatLvl)
          "end scrut_loc.\n"
          foldlM
          ( \(acc1, acc2, acc3, mi1, mi2, tenvi) (key@(dcon', idx), loc) -> do
              let idx_elem = fromJust $ L.elemIndex (key, loc) (getAllFieldLocsSoA scrut_loc)
              let case_var_loc = if dcon' == dcon 
                                 then Just $ vlocs1 !! idx
                                 else Nothing
              field_var <- gensym $ toVar $ (fromVar "soa_field_") ++ (show idx_elem)
              let acc3' = dbgTrace (minChatLvl) "print loc: " dbgTrace (minChatLvl) (sdoc (loc, scrut_loc)) dbgTrace (minChatLvl) "End cursorize print loc.\n" M.insert (fromLocVarToFreeVarsTy loc) field_var acc3
              let field_cursor_ty = getCursorizeTyFromLocVar Nothing useMutableCursorsCall loc
              let (start, end, _) = getIndexPositionOfSoALocVar useMutableCursorsCall Nothing (getAllFieldLocsSoA scrut_loc) loc
              (field_var', acc3'', field_let, mi1', mi2', tenv_handle_indexing) <- handleIndexingSoACursors tenvi case_var_loc mi1 mi2 useMutableCursorsCall (loc, field_var) (start, end) scrut_loc acc3'
              --let field_let = [(field_var, [], field_cursor_ty, Ext $ IndexCursorArray scrtCur (1 + idx_elem))]
              let curr_window = dbgTrace (minChatLvl) "Print environments: " dbgTrace (minChatLvl) (sdoc (mi2', loc, field_var, tenv_handle_indexing)) dbgTrace (minChatLvl) "End printing environments after handleIndexingSoACursors.\n" [((dcon', idx), field_var')]
              return (acc1 ++ field_let, acc2 ++ curr_window, acc3'', mi1', mi2', tenv_handle_indexing)
          )
          ([], [], freeVarToVarEnv, m1, m2, tenv1)
          (getAllFieldLocsSoA scrut_loc)
      dcon_end <- gensym "dcon_end"
      let dcon_end_let = (dcon_end, [], CursorTy, Ext $ AddCursor dcon_var (LitE 1))
      bod <-
        ( if isAbsRANDataCon dcon
            then do      
              unpackWithAbsRAN tenv1' aliveBuffers m1' m2' (SoAWin dcon_end field_v_lst) freeVarToVarEnv'
            else
              if isRelRANDataCon dcon
                then unpackWithRelRAN field_cur
                else unpackRegularDataCon tenv1' aliveBuffers m1' m2' (SoAWin dcon_var field_v_lst) freeVarToVarEnv'
        )
      let lets = mkLets ([dcon_end_let] ++ field_lets) bod
      dbgTrace (minChatLvl) "Print scrut loc: " dbgTrace (minChatLvl) (sdoc scrut_loc) dbgTrace (minChatLvl) "End loc\n" return (dcon, [], lets)
    PackedTy tycon locationVar -> case locationVar of
      Single _ ->
        (dcon,[],)
          -- Advance the cursor by 1 byte so that it points to the first field
          <$> mkLets [(field_cur, [], CursorTy, Ext $ AddCursor scrtCur (LitE 1))]
          <$> ( if isAbsRANDataCon dcon
                  then unpackWithAbsRAN tenv1 aliveBuffers m1 m2 (AoSWin field_cur) freeVarToVarEnv
                  else
                    if isRelRANDataCon dcon
                      then unpackWithRelRAN field_cur
                      else unpackRegularDataCon tenv1 aliveBuffers m1 m2 (AoSWin field_cur) freeVarToVarEnv
              )
      SoA _ _ -> do
        -- dcon_var <- gensym "dcon"
        let first_var = dbgTrace (minChatLvl) "Print scrutCur " dbgTrace (minChatLvl) (sdoc (scrtCur, ty_of_scrut, field_cur)) dbgTrace (minChatLvl) "End print scrutCur 2.\n" field_cur
        let scrut_loc = locationVar
        -- let dcon_let = [(dcon_var, [], CursorTy, Ext $ IndexCursorArray scrtCur 0)]
        -- In case of any mutable variable, we also need to update the m1 and m2 env.
        -- Vidush TODO.
        (field_lets, field_v_lst, freeVarToVarEnv', m1', m2', tenv1') <-
          dbgTrace
            (minChatLvl)
            "Print scrut_loc "
            dbgTrace
            (minChatLvl)
            (sdoc ((dcon, scrut_loc)))
            dbgTrace
            (minChatLvl)
            "end scrut_loc.\n"
            foldlM
            ( \(acc1, acc2, acc3, mi1, mi2, tenvi) (key@(dcon', idx), loc) -> do
                let idx_elem = fromJust $ L.elemIndex (key, loc) (getAllFieldLocsSoA scrut_loc)
                field_var <- gensym $ toVar $ (fromVar "soa_field_") ++ (show idx_elem)
                let acc3' = dbgTrace (minChatLvl) "print loc: " dbgTrace (minChatLvl) (sdoc (loc, scrut_loc)) dbgTrace (minChatLvl) "End cursorize print loc.\n" M.insert (fromLocVarToFreeVarsTy loc) field_var acc3
                let field_cursor_ty = getCursorizeTyFromLocVar Nothing useMutableCursorsCall loc
                let field_cursor_ty2 = getCursorizeTyFromLocVar' Nothing useMutableCursorsCall loc
                let scrut_loc_is_mutable = M.member scrut_loc mi1
                (field_var', field_let, tenvi') <- case scrut_loc_is_mutable of
                                                  True -> do 
                                                           deref_field_var <- gensym "deref"
                                                           let field_cursor_ty' = getCursorizeTyFromLocVar (Just OutputMutable) useMutableCursorsCall loc
                                                           let field_cursor_ty2' = getCursorizeTyFromLocVar' (Just OutputMutable) useMutableCursorsCall loc
                                                           let tenvi_inner = M.insert field_var field_cursor_ty2' tenvi
                                                           return (deref_field_var, [(deref_field_var, [], field_cursor_ty', Ext $ AddrOfCursor $ Ext $ IndexCursorArray scrtCur (1 + idx_elem))], M.insert deref_field_var field_cursor_ty2' tenvi_inner)
                                                  False -> return (field_var, [(field_var, [], field_cursor_ty, Ext $ IndexCursorArray scrtCur (1 + idx_elem))], M.insert field_var field_cursor_ty2 tenvi)
                let curr_window = [((dcon', idx), field_var')]
                return (acc1 ++ field_let, acc2 ++ curr_window, acc3', mi1, mi2, tenvi')
            )
            ([], [], freeVarToVarEnv, m1, m2, tenv1)
            (getAllFieldLocsSoA scrut_loc)
        dcon_end <- gensym "dcon_end"
        let dcon_end_let = (dcon_end, [], CursorTy, Ext $ AddCursor dcon_var (LitE 1))
        bod <-
          ( if isAbsRANDataCon dcon
              then unpackWithAbsRAN tenv1' aliveBuffers m1' m2' (SoAWin dcon_end field_v_lst) freeVarToVarEnv'
              else
                if isRelRANDataCon dcon
                  then unpackWithRelRAN field_cur
                  else unpackRegularDataCon tenv1' aliveBuffers m1' m2' (SoAWin dcon_var field_v_lst) freeVarToVarEnv'
          )
        let lets = mkLets ([dcon_end_let] ++ field_lets) bod
        return (dcon, [], lets)
    _ ->
      dbgTrace (minChatLvl) "Print scrutCur " dbgTrace (minChatLvl) (sdoc (scrtCur, ty_of_scrut, field_cur)) dbgTrace (minChatLvl) "End print scrutCur 3.\n" (dcon,[],)
        -- Advance the cursor by 1 byte so that it points to the first field
        <$> mkLets [(field_cur, [], CursorTy, Ext $ AddCursor scrtCur (LitE 1))]
        <$> ( if isAbsRANDataCon dcon
                then unpackWithAbsRAN tenv1 aliveBuffers m1 m2 (AoSWin field_cur) freeVarToVarEnv
                else
                  if isRelRANDataCon dcon
                    then unpackWithRelRAN field_cur
                    else unpackRegularDataCon tenv1 aliveBuffers m1 m2 (AoSWin field_cur) freeVarToVarEnv
            )
  where
    tys1 = lookupDataCon ddfs dcon
    processRhs m1pr m2pr fenvpr denv env =
      if isPacked
        then do 
          (rhs', _, m1' , m2') <- cursorizePackedExp m1pr m2pr useMutableCursorsCall emitScalarCountBumps insideTimeIt fenvpr lenv ddfs fundefs denv env senv rhs
          pure (fromDi rhs', m1', m2')
        else do 
          (rhs', _, m1', m2') <- cursorizeExp m1pr m2pr useMutableCursorsCall emitScalarCountBumps insideTimeIt fenvpr lenv ddfs fundefs denv env senv rhs
          pure (rhs', m1', m2') 

    lookupVariable :: FreeVarsTy -> M.Map FreeVarsTy Var -> PassM Var
    lookupVariable loc fenv = case (M.lookup loc fenv) of
      Just v -> return v
      Nothing -> error "lookupVariable: unexpected location variable"

    -- Since this constructor does not have random access nodes, we may not be able
    -- to unpack all the fields. Basically, anything after the first packed
    -- value isn't accessible since we have no way to reach it without knowing
    -- the end of the packed value. So we punt on creating bindings for such
    -- variables, and add them to the dependency environment instead. Later, when
    -- the appropriate end locations become available (see the LetLocE cases),
    -- these bindings are discharged from the dependency environment.
    --
    -- We recurse over the fields in `go`, and create bindings as long as we `canBind`.
    -- Otherwise, we add things to the dependency environment. `canBind` is set
    -- to true initially, and we flip it as soon as we see a packed value.
    --
    unpackRegularDataCon :: M.Map Var Ty2 -> S.Set (DataCon, Int) -> MutableLocPtsToEnv -> MutableLocOldValueEnv -> WindowIntoCursor -> M.Map FreeVarsTy Var -> PassM Exp3
    unpackRegularDataCon tenv1' aliveBuffersi m1 m2 field_cur freeVarToVarEnv_unpack = do
      -- let tenv1'' = case field_cur of
      --       AoSWin cf -> (M.insert cf (MkTy2 CursorTy) tenv1')
      --       SoAWin dcf fieldfvs ->
      --         let tenv1'' = M.insert dcf (MkTy2 CursorTy) tenv1
      --          in foldr (\(x, y) acc -> M.insert y (MkTy2 CursorTy) acc) tenv1'' fieldfvs
      (exp_unp, _, _) <- go m1 m2 field_cur freeVarToVarEnv_unpack vlocs1 tys1 True denv1 tenv1'
      return exp_unp
      where
        rhsUsesTraverse :: Bool
        rhsUsesTraverse = usesTraverseCall rhs

        rhsVarsMentioned :: S.Set Var
        rhsVarsMentioned = varsMentionedInExp rhs

        vlocToIndex :: M.Map (Var, LocArg) Int
        vlocToIndex = M.fromList (zip vlocs1 [0..])

        lookupFieldIdx :: (Var, LocArg) -> Int
        lookupFieldIdx vl =
          case M.lookup vl vlocToIndex of
            Just idx -> idx
            Nothing -> error $ "unpackRegularDataCon: missing field index for " ++ sdoc vl

        -- Vidush: Change function signature to return the mutable loc pts to envs etc.
        go :: MutableLocPtsToEnv -> MutableLocOldValueEnv -> WindowIntoCursor -> M.Map FreeVarsTy Var -> [(Var, LocArg)] -> [Ty2] -> Bool -> DepEnv -> TyEnv Var Ty2 -> PassM (Exp3, MutableLocPtsToEnv, MutableLocOldValueEnv)
        go m1 m2 curw fenv vlocs tys canBind denv tenv = do
          case curw of
            AoSWin cur -> do
              case (vlocs, tys) of
                ([], []) -> processRhs m1 m2 fenv denv tenv
                ((v, locarg) : rst_vlocs, (MkTy2 ty) : rst_tys) ->
                  let loc = fromLocArgToFreeVarsTy locarg
                   in case ty of
                        -- Int, Float, Sym, or Bool
                        -- Vidush: Handle mutable input cases for tail recursion: TODO.
                        _ | isScalarTy ty -> do
                          loc_var <- lookupVariable loc fenv
                          if canBind
                            then do
                              -- If the location exists in the environment, it indicates that the
                              -- corresponding variable was also bound and we shouldn't create duplicate
                              -- bindings (checked in the LetLocE cases).
                              loc_var <- lookupVariable loc fenv
                              -- here we need to make sure that any mutable loc pointing to cur 
                              -- is aliased to loc_var now.
                              let mut_loc = findMutableLocationPointingToVar cur m1
                              m1' <- case mut_loc of 
                                            Nothing -> dbgTrace (minChatLvl) "Print inside unpackRegularDataCon AoS Scalar: " dbgTrace (minChatLvl) (sdoc (mut_loc, loc, cur)) dbgTrace (minChatLvl) "End printing inside unpackRegularDcon AoS Scalar!\n" return m1 
                                            Just l -> do 
                                                       let m1inner = updateMutableLocPtsToEnv l m1 (loc_var, Just l, Nothing, S.singleton cur) True
                                                       dbgTrace (minChatLvl) "Print inside unpackRegularDataCon AoS Scalar: " dbgTrace (minChatLvl) (sdoc (mut_loc, loc, cur)) dbgTrace (minChatLvl) "End printing inside unpackRegularDcon AoS Scalar 2!\n" return m1inner
                              (tenv', binds, m1'', m2') <- scalarBinds True fenv m1' m2 ty v loc_var locarg tenv
                              let binds' = ((loc_var), [], CursorTy, VarE cur) : binds    
                              let tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                              (bod, m1''', m2'') <- go m1'' m2' (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv tenv''
                              return (mkLets binds' bod, m1''', m2'')
                            else do
                              -- Cannot read this int. Instead, we add it to DepEnv.
                              (tenv', binds, m1', m2') <- scalarBinds True fenv m1 m2 ty v loc_var locarg tenv
                              let denv' = M.insertWith (++) (loc) binds denv
                              go m1' m2' (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv' tenv'

                        -- An indirection or redirection pointer.
                        -- ASSUMPTION: We can always bind it, since it occurs immediately after the tag.
                        CursorTy -> do
                          tmp <- gensym "readcursor_indir"
                          loc_var <- lookupVariable loc fenv
                          let tenv' =
                                M.union
                                  ( M.fromList
                                      [ (tmp, MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                        ((loc_var), MkTy2 CursorTy),
                                        (v, MkTy2 CursorTy),
                                        (toEndV v, MkTy2 CursorTy),
                                        (toTagV v, MkTy2 IntTy),
                                        (toEndFromTaggedV v, MkTy2 CursorTy)
                                      ]
                                  )
                                  tenv
                              read_cursor =
                                if isIndirectionTag dcon || isRedirectionTag dcon
                                  then Ext (ReadTaggedCursor cur)
                                  else error $ "unpackRegularDataCon: cursorty without indirection/redirection."  
                              binds =
                                [ (tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                  ((loc_var), [], CursorTy, VarE cur),
                                  (v, [], CursorTy, ProjE 0 (VarE tmp)),
                                  (toEndV v, [], CursorTy, ProjE 1 (VarE tmp)),
                                  (toTagV v, [], IntTy, ProjE 2 (VarE tmp)),
                                  (toEndFromTaggedV v, [], CursorTy, Ext $ AddCursor v (VarE (toTagV v)))
                                ]
                          let mut_loc = findMutableLocationPointingToVar cur m1
                          (m1', bnds') <- case mut_loc of 
                                            Nothing -> dbgTrace (minChatLvl) "Print inside unpackRegularDataCon AoS Scalar: " dbgTrace (minChatLvl) (sdoc (mut_loc, loc, cur)) dbgTrace (minChatLvl) "End printing inside unpackRegularDcon AoS Scalar!\n" return (m1, []) 
                                            Just l -> do 
                                                       let m1inner = updateMutableLocPtsToEnv l m1 (v, Just l, Nothing, S.empty) False
                                                       void_var <- gensym "void_"
                                                       let lname = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy l)
                                                       let bnds = [(void_var, [], ProdTy [], Ext $ WriteCursorMutable lname (VarE v))]
                                                       dbgTrace (minChatLvl) "Print inside unpackRegularDataCon AoS Scalar: " dbgTrace (minChatLvl) (sdoc (mut_loc, loc, cur)) dbgTrace (minChatLvl) "End printing inside unpackRegularDcon AoS Scalar 2!\n" return (m1inner, bnds)
                          (bod, m1'', m2') <- go m1' m2 (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv tenv'
                          return (mkLets (binds ++ bnds') bod, m1'', m2')
                        VectorTy el_ty -> do
                          tmp <- gensym "read_vec_tuple"
                          loc_var <- lookupVariable loc fenv
                          let tenv' =
                                M.union
                                  ( M.fromList
                                      [ (tmp, MkTy2 (ProdTy [VectorTy el_ty, CursorTy])),
                                        (v, MkTy2 (VectorTy el_ty)),
                                        (toEndV v, MkTy2 CursorTy)
                                      ]
                                  )
                                  tenv
                              ty' = stripTyLocs ty
                              binds =
                                [ (tmp, [], ProdTy [ty', CursorTy], Ext $ ReadVector (loc_var) (stripTyLocs el_ty)),
                                  (v, [], ty', ProjE 0 (VarE tmp)),
                                  (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))
                                ]
                          if canBind
                            then do
                              -- If the location exists in the environment, it indicates that the
                              -- corresponding variable was also bound and we shouldn't create duplicate
                              -- bindings (checked in the LetLocE cases).
                              loc_var <- lookupVariable loc fenv
                              let binds' = ((loc_var), [], CursorTy, VarE cur) : binds
                                  tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                              (bod, m1', m2') <- go m1 m2 (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv tenv''
                              return (mkLets binds' bod, m1', m2')
                            else do
                              -- Cannot read this int. Instead, we add it to DepEnv.
                              let denv' = M.insertWith (++) (loc) binds denv
                              go m1 m2 (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv' tenv'
                        ListTy el_ty -> do
                          tmp <- gensym "read_list_tuple"
                          loc_var <- lookupVariable loc fenv
                          let tenv' =
                                M.union
                                  ( M.fromList
                                      [ (tmp, MkTy2 (ProdTy [ListTy el_ty, CursorTy])),
                                        (v, MkTy2 (ListTy el_ty)),
                                        (toEndV v, MkTy2 CursorTy)
                                      ]
                                  )
                                  tenv
                              ty' = stripTyLocs ty
                              binds =
                                [ (tmp, [], ProdTy [ty', CursorTy], Ext $ ReadList (loc_var) (stripTyLocs el_ty)),
                                  (v, [], ty', ProjE 0 (VarE tmp)),
                                  (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))
                                ]
                          if canBind
                            then do
                              -- If the location exists in the environment, it indicates that the
                              -- corresponding variable was also bound and we shouldn't create duplicate
                              -- bindings (checked in the LetLocE cases).
                              loc_var <- lookupVariable loc fenv
                              let binds' = ((loc_var), [], CursorTy, VarE cur) : binds
                                  tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                              (bod, m1', m2') <- go m1 m2 (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv tenv''
                              return (mkLets binds' bod, m1', m2')
                            else do
                              -- Cannot read this int. Instead, we add it to DepEnv.
                              let denv' = M.insertWith (++) (loc) binds denv
                              go m1 m2 (AoSWin (toEndV v)) fenv rst_vlocs rst_tys canBind denv' tenv'
                        PackedTy _ ploc -> do
                          let tenv' = M.insert v (MkTy2 CursorTy) tenv
                          loc_var <- lookupVariable loc fenv
                          if canBind
                            then do
                              let tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                              -- Flip canBind to indicate that the subsequent fields
                              -- should be added to the dependency environment.
                              let mut_loc = findMutableLocationPointingToVar cur m1
                              m1' <- case mut_loc of 
                                            Nothing -> dbgTrace (minChatLvl) "Print inside unpackRegularDataCon AoS Scalar: " dbgTrace (minChatLvl) (sdoc (mut_loc, loc, cur)) dbgTrace (minChatLvl) "End printing inside unpackRegularDcon AoS Scalar!\n" return m1 
                                            Just l -> do 
                                                       let m1inner = updateMutableLocPtsToEnv l m1 (v, Just l, Nothing, S.fromList [cur, loc_var]) True
                                                       dbgTrace (minChatLvl) "Print inside unpackRegularDataCon AoS Scalar: " dbgTrace (minChatLvl) (sdoc (mut_loc, loc, cur)) dbgTrace (minChatLvl) "End printing inside unpackRegularDcon AoS Scalar 2!\n" return m1inner
                              (bod, m1'', m2') <- go m1' m2 (AoSWin (toEndV v)) fenv rst_vlocs rst_tys False denv tenv''
                              return (
                                mkLets
                                  [ ((loc_var), [], CursorTy, VarE cur),
                                    (v, [], CursorTy, VarE (loc_var))
                                  ]
                                  bod, m1'', m2')
                            else do
                              -- Cannot read this. Instead, we add it to DepEnv.
                              -- let mut_loc = findMutableLocationPointingToEndVar cur m1
                              -- m1' <- case mut_loc of 
                              --               Nothing -> dbgTrace (minChatLvl) "Print inside unpackRegularDataCon AoS Scalar: " dbgTrace (minChatLvl) (sdoc (mut_loc, loc, cur, m1)) dbgTrace (minChatLvl) "End printing inside unpackRegularDcon AoS False can bind Scalar!\n" return m1 
                              --               Just l -> do 
                              --                          let m1inner = updateMutableLocPtsToEnv l m1 (v, Just l, Nothing, S.fromList [cur, loc_var]) True
                              --                          dbgTrace (minChatLvl) "Print inside unpackRegularDataCon AoS Scalar: " dbgTrace (minChatLvl) (sdoc (mut_loc, loc, cur)) dbgTrace (minChatLvl) "End printing inside unpackRegularDcon AoS False can bind Scalar 2!\n" return m1inner
                              let denv' = M.insertWith (++) (loc) [(v, [], CursorTy, VarE (loc_var))] denv
                              go m1 m2 (AoSWin (toEndV v)) fenv rst_vlocs rst_tys False denv' tenv'
                        _ -> error $ "unpackRegularDataCon: Unexpected field " ++ sdoc (v, loc) ++ ":" ++ sdoc ty
                _ -> error $ "unpackRegularDataCon: Unexpected numnber of varible, type pairs: " ++ show (vlocs, tys)
            {- VS: TODO: handle other cases. Right now, it is only scalar and packed -}
            SoAWin dcur _field_cur -> do
              case (vlocs, tys) of
                ([], []) -> processRhs m1 m2 fenv denv tenv
                ((v, locarg) : rst_vlocs, (MkTy2 ty) : rst_tys) ->
                  let loc = fromLocArgToFreeVarsTy locarg
                      reg = toRegVar locarg
                   in case ty of
                        -- Int, Float, Sym, or Bool
                        _ | isScalarTy ty -> do
                          let isVarAlive = isNoDeadFieldElim denv || rhsUsesTraverse || S.member v rhsVarsMentioned
                          loc_var <- lookupVariable loc fenv
                          -- This won't work 
                          -- VS: We need to take union of all branches 
                          -- Traverse variables used there 
                          -- Except for indirection or redirectin pointers
                          --let free_vars_rhs = allFreeVars rhs
                          --let var_used = dbgTrace (minChatLvl) "Print free vars: " dbgTrace (minChatLvl) (sdoc (free_vars_rhs, rhs)) dbgTrace (minChatLvl) "End free vars.\n" S.member (V v) free_vars_rhs
                          --(tenv', binds) <- if var_used 
                          --                  then scalarBinds ty v loc_var tenv
                          --                  else return (tenv, [])
                          (tenv', binds, m1', m2') <- scalarBinds isVarAlive fenv m1 m2 ty v loc_var locarg tenv
                          let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                          let field_cur' = map (\(k@(d, idx), var) -> if ((d, idx) == (dcon, field_idx)) {-&& var_used-} 
                                                                      then (k, (toEndV v))
                                                                      else (k, var)) _field_cur
                          let cur = dbgTrace (minChatLvl) "Print in scalar ty: " dbgTrace (minChatLvl) (sdoc (binds, loc_var, loc, v, isVarAlive)) dbgTrace (minChatLvl) "End in scalar ty SoA unpackDcon!\n." fromJust $ L.lookup (dcon, field_idx) _field_cur
                          if canBind
                            then do
                              -- If the location exists in the environment, it indicates that the
                              -- corresponding variable was also bound and we shouldn't create duplicate
                              -- bindings (checked in the LetLocE cases).
                              loc_var <- lookupVariable loc fenv
                              let binds' = ((loc_var), [], CursorTy, VarE cur) : binds
                                  tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'

                              (bod, m1'', m2'') <- go m1' m2' (SoAWin dcur field_cur') fenv rst_vlocs rst_tys canBind denv tenv''
                              return (mkLets binds' bod, m1'', m2'')
                            else do
                              -- Cannot read this int. Instead, we add it to DepEnv.
                              let denv' = M.insertWith (++) (loc) binds denv
                              go m1' m2' (SoAWin dcur field_cur') fenv rst_vlocs rst_tys canBind denv' tenv'

                        -- An indirection or redirection pointer.
                        -- ASSUMPTION: We can always bind it, since it occurs immediately after the tag.
                        CursorTy -> do
                          if isRedirectionTag dcon
                            then do
                              tmp <- dbgTrace (minChatLvl) "Print field_cur: " dbgTrace (minChatLvl) (sdoc (dcur, _field_cur)) dbgTrace (minChatLvl) "End FieldCur\n" gensym "readcursor_indir"
                              tmp_flds <- mapM (\((dcon, idx), _) -> gensym "readcursor_indir_flds") _field_cur
                              loc_var <- lookupVariable loc fenv
                              var_dcon_next <- gensym "dcon_next"
                              vars_next_fields <- mapM (\((dcon, idx), _) -> gensym "field_nxt") _field_cur
                              redirection_var_dcon <- gensym "dcon_redir"
                              res <- mapM (\((dcon, idx), _loc) -> do
                                                                               let locTy = (lookupDataCon ddfs dcon) !! idx
                                                                               case locTy of 
                                                                                                MkTy2 (PackedTy _ loc) -> do
                                                                                                                          let lty = getCursorizeTyFromLocVar Nothing useMutableCursorsCall loc
                                                                                                                          case lty of 
                                                                                                                               CursorTy -> do
                                                                                                                                            new_var <- gensym "fld_redir"
                                                                                                                                            return $ ((dcon, idx), _loc, [new_var])
                                                                                                                               CursorArrayTy _sz -> do  
                                                                                                                                                    num_vars <- mapM (\i -> do 
                                                                                                                                                          var <- gensym "new"
                                                                                                                                                          return var
                                                                                                                                                          ) [1.._sz] 
                                                                                                                                                    return $ ((dcon, idx), _loc, num_vars) 
                                                                                                MkTy2 (CursorArrayTy _sz) -> do
                                                                                                                             num_vars <- mapM (\i -> do 
                                                                                                                                                     var <- gensym "new"
                                                                                                                                                     return var
                                                                                                                                              ) [1.._sz] 
                                                                                                                             return $ ((dcon, idx), _loc, num_vars)
                                                                                                _ -> do 
                                                                                                     new_var <- gensym "fld_redir"
                                                                                                     return $ ((dcon, idx), _loc, [new_var])
                                                                ) _field_cur
                              let redirection_var_flds = concatMap thd3 res
                              -- let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                              -- let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur
                              let tenv' =
                                    M.union
                                      ( M.fromList
                                          [ (tmp, MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                            -- ((loc_var)     , MkTy2 CursorTy),
                                            (redirection_var_dcon, MkTy2 CursorTy),
                                            (toEndV redirection_var_dcon, MkTy2 CursorTy),
                                            (toTagV redirection_var_dcon, MkTy2 IntTy),
                                            (toEndFromTaggedV redirection_var_dcon, MkTy2 CursorTy)
                                          ]
                                      )
                                      tenv
                                  read_cursor =
                                    if isIndirectionTag dcon || isRedirectionTag dcon
                                      then Ext (ReadTaggedCursor var_dcon_next)
                                      else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                                  -- v is the variable i want to send to the call.
                                  -- In this case v is the soa variable where all redirections are unpacked.

                                  -- Vidush: We need to update the mutable env accordingly here.
                                  mut_loc_pointing_to_dcur = findMutableLocationPointingToVar dcur m1
                                  (binds, m1d) = case mut_loc_pointing_to_dcur of 
                                                      Nothing -> ([ (var_dcon_next, [], CursorTy, Ext (AddCursor dcur (LitE 1))),
                                                                   (tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                                                   ((loc_var), [], CursorTy, VarE dcur),
                                                                   (redirection_var_dcon, [], CursorTy, ProjE 0 (VarE tmp)),
                                                                   (toEndV redirection_var_dcon, [], CursorTy, ProjE 1 (VarE tmp)),
                                                                   (toTagV redirection_var_dcon, [], IntTy, ProjE 2 (VarE tmp)),
                                                                   (toEndFromTaggedV redirection_var_dcon, [], CursorTy, Ext $ AddCursor redirection_var_dcon (VarE (toTagV redirection_var_dcon)))
                                                                 ], m1)
                                                      Just l -> let
                                                                 lName = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy l)
                                                                 m1' = updateMutableLocPtsToEnv l m1 (redirection_var_dcon, Just l, Nothing, S.empty) False
                                                                 in ([ (var_dcon_next, [], CursorTy, Ext (AddCursor dcur (LitE 1))),
                                                                   (tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                                                   ((loc_var), [], CursorTy, VarE dcur),
                                                                   (redirection_var_dcon, [], CursorTy, ProjE 0 (VarE tmp)),
                                                                   ("_", [], ProdTy [], Ext $ WriteCursorMutable lName (VarE redirection_var_dcon)),
                                                                   (toEndV redirection_var_dcon, [], CursorTy, ProjE 1 (VarE tmp)),
                                                                   (toTagV redirection_var_dcon, [], IntTy, ProjE 2 (VarE tmp)),
                                                                   (toEndFromTaggedV redirection_var_dcon, [], CursorTy, Ext $ AddCursor redirection_var_dcon (VarE (toTagV redirection_var_dcon)))
                                                                  ], m1')

                                  -- generate binds for all fields.
                                  (_, binds_flields, m1', m2') =
                                    L.foldl
                                      ( \(index, res, m1i, m2i) ((dcon', idx), var, redir_vars) ->
                                          let read_cursor_f =
                                                if isIndirectionTag dcon || isRedirectionTag dcon
                                                  then Ext (ReadTaggedCursor (vars_next_fields !! index))
                                                  else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                                              tmpf = tmp_flds !! index
                                              ty_of_field = (lookupDataCon ddfs dcon') !! idx
                                              redirection_var_flds_variable = redirection_var_flds !! index
                                           in case ty_of_field of
                                                (MkTy2 PackedTy {}) ->
                                                  let (new_binds, m1iout) = case redir_vars of 
                                                                          [v] -> let var_pts_mutl = findMutableLocationPointingToVar var m1i
                                                                                  in case var_pts_mutl of 
                                                                                            Nothing -> ([(redirection_var_flds_variable, [], CursorTy, Ext (AddCursor var (LitE 0)))], m1i)
                                                                                            Just ml -> let m1i' = updateMutableLocPtsToEnv ml m1i (redirection_var_flds_variable, Just ml, Nothing, S.singleton var) True
                                                                                                           bnd = [(redirection_var_flds_variable, [], CursorTy, Ext (AddCursor var (LitE 0)))]
                                                                                                        in (bnd, m1i')
                                                                          rst -> let (bndsi, m1i') = (map (\v -> (v, [], CursorTy, Ext (IndexCursorArray var (fromJust $ L.elemIndex v rst)))) rst, m1i')
                                                                                   in (bndsi, m1i')
                                                                   in (index + L.length (redir_vars), res ++ new_binds, m1iout, m2i)
                                                (MkTy2 CursorArrayTy {}) ->
                                                  let (new_binds, m1iout) = case redir_vars of 
                                                                            [v] -> let var_pts_mutl = findMutableLocationPointingToVar var m1i
                                                                                    in case var_pts_mutl of 
                                                                                                Nothing -> ([(redirection_var_flds_variable, [], CursorTy, Ext (AddCursor var (LitE 0)))], m1i)
                                                                                                Just ml -> let m1i' = updateMutableLocPtsToEnv ml m1i (redirection_var_flds_variable, Just ml, Nothing, S.singleton var) True
                                                                                                               bnd = [(redirection_var_flds_variable, [], CursorTy, Ext (AddCursor var (LitE 0)))]
                                                                                                            in (bnd, m1i')
                                                                            rst -> let (bndsi, m1i') = (map (\v -> (v, [], CursorTy, Ext (IndexCursorArray var (fromJust $ L.elemIndex v rst)))) rst, m1i')
                                                                                    in (bndsi, m1i')
                                                   in (index + L.length (redir_vars), res ++ new_binds, m1iout, m2i)
                                                _ ->
                                                  let (new_binds, m1out) = case redir_vars of 
                                                                        [v] -> let mut_loc_pts_var = dbgTrace (minChatLvl) "Print in redirection SoA: " dbgTrace (minChatLvl) (sdoc (var, m1i)) dbgTrace (minChatLvl) "End in redirection SoA.\n" findMutableLocationPointingToVar var m1i
                                                                                in case mut_loc_pts_var of 
                                                                                          Nothing -> let bnds = [ (vars_next_fields !! index, [], CursorTy, Ext (AddCursor var (LitE 1))),
                                                                                                                  (tmpf, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor_f),
                                                                                                                  -- ((loc_var)     , [], CursorTy, VarE dcur),
                                                                                                                  (redirection_var_flds_variable, [], CursorTy, ProjE 0 (VarE tmpf)),
                                                                                                                  (toEndV redirection_var_flds_variable, [], CursorTy, ProjE 1 (VarE tmpf)),
                                                                                                                  (toTagV redirection_var_flds_variable, [], IntTy, ProjE 2 (VarE tmpf)),
                                                                                                                  (toEndFromTaggedV redirection_var_flds_variable, [], CursorTy, Ext $ AddCursor redirection_var_flds_variable (VarE (toTagV redirection_var_flds_variable)))
                                                                                                                ]
                                                                                                       in (bnds, m1i)
                                                                                          Just ml -> let m1i' = updateMutableLocPtsToEnv ml m1i (redirection_var_flds_variable, Just ml, Nothing, S.empty) False
                                                                                                         isFieldAlive = S.member (dcon', idx) aliveBuffersi
                                                                                                         -- write to the mutable location, we need to write the redirection_var_flds_variable value.
                                                                                                         mlName = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy ml)
                                                                                                         bnd_write_to_mut_var = if isFieldAlive
                                                                                                                                then [("_", [], ProdTy [], Ext $ WriteCursorMutable mlName (VarE redirection_var_flds_variable))]
                                                                                                                                else []
                                                                                                         bnds' = [ (vars_next_fields !! index, [], CursorTy, Ext (AddCursor var (LitE 1))),
                                                                                                                  (tmpf, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor_f),
                                                                                                                  -- ((loc_var)     , [], CursorTy, VarE dcur),
                                                                                                                  (redirection_var_flds_variable, [], CursorTy, ProjE 0 (VarE tmpf))] ++ 
                                                                                                                  bnd_write_to_mut_var ++ 
                                                                                                                 [(toEndV redirection_var_flds_variable, [], CursorTy, ProjE 1 (VarE tmpf)),
                                                                                                                  (toTagV redirection_var_flds_variable, [], IntTy, ProjE 2 (VarE tmpf)),
                                                                                                                  (toEndFromTaggedV redirection_var_flds_variable, [], CursorTy, Ext $ AddCursor redirection_var_flds_variable (VarE (toTagV redirection_var_flds_variable)))
                                                                                                                ]
                                                                                                      in (bnds', m1i')   
                                                                              
                                                                        rst -> error $ "Did not expect multiple variables for type " ++ show ty_of_field
                                                   in (index + L.length (redir_vars), res ++ new_binds, m1out, m2i)
                                      )
                                      (0, [], m1d, m2)
                                      res
                                  -- Vidush : TODO this needs to change since type changed
                                  soa_redir_bind = [(v, [], CursorArrayTy (1 + length (redirection_var_flds)), mkMakeCursorArrayDbg v ([redirection_var_dcon] ++ redirection_var_flds))]
                                  mut_loc_in_same_reg = findMutableLocationInSameRegion reg m1'
                                  m1'' = case mut_loc_in_same_reg of 
                                                    Nothing -> m1' 
                                                    Just (_v, lv) -> let m1i = updateMutableLocPtsToEnv lv m1' (v, Just lv, Nothing, S.empty) False
                                                                      in m1i

                                  tenv'' =
                                    M.union
                                      ( M.fromList
                                          [ (v, MkTy2 $ CursorArrayTy (1 + length (redirection_var_flds)))
                                          ]
                                      )
                                      tenv
                              (bod, m1''', m2'') <- go m1'' m2' curw fenv rst_vlocs rst_tys canBind denv tenv'' -- (toEndV v)
                              return (mkLets (binds ++ binds_flields ++ soa_redir_bind) bod, m1''', m2'')
                            else
                              -- This case is different for when the GC is on. 
                              -- Vidush: TODO change this when the GC is on
                              if isIndirectionTag dcon
                                then do
                                   dflags <- getDynFlags
                                   if gopt Opt_DisableGC dflags
                                   then do 
                                    tmp <- gensym "readcursor_indir"
                                    loc_var <- lookupVariable loc fenv
                                    let locs_ty = case (loc) of
                                          FL l -> getCursorizeTyFromLocVar' Nothing useMutableCursorsCall l
                                          _ -> error "Expected location!"
                                    let locs_ty3 :: Ty3 = case (loc) of
                                          FL l -> getCursorizeTyFromLocVar Nothing useMutableCursorsCall l
                                          _ -> error "Expected location!"
                                    -- let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                                    -- let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur
                                    var_dcon_next <- gensym "dcon_next"
                                    let tenv' =
                                          M.union
                                            ( M.fromList
                                                [ (tmp, MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                                 ((loc_var), locs_ty),
                                                 (v,  locs_ty)
                                                 -- (toEndV v, MkTy2 CursorTy),
                                                 -- (toTagV v, MkTy2 IntTy),
                                                 -- (toEndFromTaggedV v, MkTy2 CursorTy)
                                               ]
                                            )
                                            tenv
                                        read_cursor =
                                          if isIndirectionTag dcon || isRedirectionTag dcon
                                            then Ext (ReadTaggedCursor var_dcon_next)
                                            else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                                        mut_loc_pointing_to_dcur = findMutableLocationPointingToVar dcur m1    
                                        (binds, m1d) = case mut_loc_pointing_to_dcur of 
                                                              Nothing -> ([ (var_dcon_next, [], CursorTy, Ext (AddCursor dcur (LitE 1))),
                                                                            --(tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                                                           (v, [], locs_ty3, Ext $ InitCursor locs_ty3),
                                                                           ("_", [], ProdTy [], Ext (MemCpy v var_dcon_next locs_ty3))
                                                                            -- ,
                                                                            -- (toEndV v, [], CursorTy, ProjE 1 (VarE tmp)),
                                                                            -- (toTagV v, [], IntTy   , ProjE 2 (VarE tmp)),
                                                                            -- End of region needs to be calculated differently
                                                                            -- (toEndFromTaggedV v, [], CursorTy, Ext $ AddCursor v (VarE (toTagV v))),
                                                                            -- ((loc_var), [], locs_ty3, VarE v)
                                                                          ], m1) 
                                                              Just l -> let 
                                                                          lName = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy l)
                                                                          m1' = updateMutableLocPtsToEnv l m1 (v, Just l, Nothing, S.empty) False
                                                                         in ([ (var_dcon_next, [], CursorTy, Ext (AddCursor dcur (LitE 1))),
                                                                               --(tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                                                               -- (v, [], locs_ty3, Ext $ InitCursor locs_ty3),
                                                                               ("_", [], ProdTy [], Ext (MemCpy lName var_dcon_next locs_ty3))
                                                                               -- ,
                                                                               -- (toEndV v, [], CursorTy, ProjE 1 (VarE tmp)),
                                                                               -- (toTagV v, [], IntTy   , ProjE 2 (VarE tmp)),
                                                                               -- End of region needs to be calculated differently
                                                                               -- (toEndFromTaggedV v, [], CursorTy, Ext $ AddCursor v (VarE (toTagV v))),
                                                                               -- ((loc_var), [], locs_ty3, VarE v)
                                                                          ], m1d)

                                          
                                    (bod, m1', m2') <- go m1d m2 curw fenv rst_vlocs rst_tys canBind denv tenv' -- (toEndV v)
                                    return (mkLets binds bod, m1', m2')
                                    -- TODO:
                                    -- Vidush: The GC case for indirection will require us to take the indirection for nested SoA locations too!
                                   else do 
                                    tmp <- dbgTrace (minChatLvl) "Print field_cur: " dbgTrace (minChatLvl) (sdoc (dcur, _field_cur)) dbgTrace (minChatLvl) "End FieldCur\n" gensym "readcursor_indir"
                                    tmp_flds <- mapM (\((dcon, idx), _) -> gensym "readcursor_indir_flds") _field_cur
                                    loc_var <- lookupVariable loc fenv
                                    var_dcon_next <- gensym "dcon_next"
                                    vars_next_fields <- mapM (\((dcon, idx), _) -> gensym "field_nxt") _field_cur
                                    redirection_var_dcon <- gensym "dcon_redir"
                                    res <- mapM (\((dcon, idx), _loc) -> do
                                                                               let locTy = (lookupDataCon ddfs dcon) !! idx
                                                                               case locTy of 
                                                                                                MkTy2 (PackedTy _ loc) -> do
                                                                                                                          let lty = getCursorizeTyFromLocVar Nothing useMutableCursorsCall loc
                                                                                                                          case lty of 
                                                                                                                               CursorTy -> do
                                                                                                                                            new_var <- gensym "fld_redir"
                                                                                                                                            return $ ((dcon, idx), _loc, [new_var])
                                                                                                                               CursorArrayTy _sz -> do  
                                                                                                                                                    num_vars <- mapM (\i -> do 
                                                                                                                                                          var <- gensym "new"
                                                                                                                                                          return var
                                                                                                                                                          ) [1.._sz] 
                                                                                                                                                    return $ ((dcon, idx), _loc, num_vars) 
                                                                                                MkTy2 (CursorArrayTy _sz) -> do
                                                                                                                             num_vars <- mapM (\i -> do 
                                                                                                                                                     var <- gensym "new"
                                                                                                                                                     return var
                                                                                                                                              ) [1.._sz] 
                                                                                                                             return $ ((dcon, idx), _loc, num_vars)
                                                                                                _ -> do 
                                                                                                     new_var <- gensym "fld_redir"
                                                                                                     return $ ((dcon, idx), _loc, [new_var])
                                                                ) _field_cur
                                    let redirection_var_flds = concatMap thd3 res
                                    -- let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                                    -- let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur
                                    let tenv' = M.union
                                                ( M.fromList
                                                  [ (tmp, MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                                  -- ((loc_var)     , MkTy2 CursorTy),
                                                    (redirection_var_dcon, MkTy2 CursorTy),
                                                    (toEndV redirection_var_dcon, MkTy2 CursorTy),
                                                    (toTagV redirection_var_dcon, MkTy2 IntTy),
                                                    (toEndFromTaggedV redirection_var_dcon, MkTy2 CursorTy)
                                                  ]
                                                ) tenv
                                        read_cursor =
                                            if isIndirectionTag dcon || isRedirectionTag dcon
                                            then Ext (ReadTaggedCursor var_dcon_next)
                                            else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                                        -- v is the variable i want to send to the call.
                                        -- In this case v is the soa variable where all redirections are unpacked.
                                        binds = [ (var_dcon_next, [], CursorTy, Ext (AddCursor dcur (LitE 1))),
                                                  (tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                                  ((loc_var), [], CursorTy, VarE dcur),
                                                  (redirection_var_dcon, [], CursorTy, ProjE 0 (VarE tmp)),
                                                  (toEndV redirection_var_dcon, [], CursorTy, ProjE 1 (VarE tmp)),
                                                  (toTagV redirection_var_dcon, [], IntTy, ProjE 2 (VarE tmp)),
                                                  (toEndFromTaggedV redirection_var_dcon, [], CursorTy, Ext $ AddCursor redirection_var_dcon (VarE (toTagV redirection_var_dcon)))
                                                ]
                                        -- generate binds for all fields.
                                        binds_flields =
                                          L.foldl
                                            ( \(index, res) ((dcon', idx), var, redir_vars) ->
                                              let read_cursor_f =
                                                      if isIndirectionTag dcon || isRedirectionTag dcon
                                                      then Ext (ReadTaggedCursor (vars_next_fields !! index))
                                                      else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                                                  tmpf = tmp_flds !! index
                                                  ty_of_field = (lookupDataCon ddfs dcon') !! idx
                                               in case ty_of_field of
                                                    (MkTy2 PackedTy {}) -> --[(v, [], CursorTy, Ext (AddCursor var (LitE 0)))]
                                                        let new_binds = case redir_vars of 
                                                                                [v] -> [ (vars_next_fields !! index, [], CursorTy, Ext (AddCursor var (LitE 1))),
                                                                                         (tmpf, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor_f),
                                                                                         -- ((loc_var)     , [], CursorTy, VarE dcur),
                                                                                         ((v), [], CursorTy, ProjE 0 (VarE tmpf)),
                                                                                         (toEndV (v), [], CursorTy, ProjE 1 (VarE tmpf)),
                                                                                         (toTagV (v), [], IntTy, ProjE 2 (VarE tmpf)),
                                                                                         (toEndFromTaggedV (v), [], CursorTy, Ext $ AddCursor (v) (VarE (toTagV (v))))
                                                                                       ]
                                                                                rst ->  map (\v -> (v, [], CursorTy, Ext (IndexCursorArray var (fromJust $ L.elemIndex v rst)))) rst
                                                         in (index + L.length (redir_vars), res ++ new_binds)
                                                    (MkTy2 CursorArrayTy {}) ->
                                                        let new_binds = case redir_vars of 
                                                                                 [v] -> [ (vars_next_fields !! index, [], CursorTy, Ext (AddCursor var (LitE 1))),
                                                                                         (tmpf, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor_f),
                                                                                         -- ((loc_var)     , [], CursorTy, VarE dcur),
                                                                                         ((v), [], CursorTy, ProjE 0 (VarE tmpf)),
                                                                                         (toEndV (v), [], CursorTy, ProjE 1 (VarE tmpf)),
                                                                                         (toTagV (v), [], IntTy, ProjE 2 (VarE tmpf)),
                                                                                         (toEndFromTaggedV (v), [], CursorTy, Ext $ AddCursor (v) (VarE (toTagV (v))))
                                                                                       ]
                                                                                 rst ->  map (\v -> (v, [], CursorTy, Ext (IndexCursorArray var (fromJust $ L.elemIndex v rst)))) rst
                                                         in (index + L.length (redir_vars), res ++ new_binds)
                                                    _ ->
                                                        let new_binds = case redir_vars of 
                                                              [v] ->
                                                                    [ (vars_next_fields !! index, [], CursorTy, Ext (AddCursor var (LitE 1))),
                                                                      (tmpf, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor_f),
                                                                      -- ((loc_var)     , [], CursorTy, VarE dcur),
                                                                      ((v), [], CursorTy, ProjE 0 (VarE tmpf)),
                                                                      (toEndV (v), [], CursorTy, ProjE 1 (VarE tmpf)),
                                                                      (toTagV (v), [], IntTy, ProjE 2 (VarE tmpf)),
                                                                      (toEndFromTaggedV (v), [], CursorTy, Ext $ AddCursor (v) (VarE (toTagV (v))))
                                                                    ]
                                                              _ -> error "Did not expect multiple variables!"
                                                         in (index + L.length (redir_vars), res ++ new_binds)
                                            ) (0, []) res
                                        soa_redir_bind = [(v, [], CursorArrayTy (1 + length (redirection_var_flds)), mkMakeCursorArrayDbg v ([redirection_var_dcon] ++ redirection_var_flds))]
                                        tenv'' = M.union
                                                ( M.fromList
                                                  [ (v, MkTy2 $ CursorArrayTy (1 + length (redirection_var_flds)))
                                                  ]
                                                ) tenv
                                    (bod, m1', m2') <- go m1 m2 curw fenv rst_vlocs rst_tys canBind denv tenv'' -- (toEndV v)
                                    return (mkLets (binds ++ (snd binds_flields) ++ soa_redir_bind) bod, m1', m2')
                                else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                        
                        -- An indirection pointer for an SoA region.
                        -- ASSUMPTION: We can always bind it, since it occurs immediately after the tag.
                        CursorArrayTy size -> do
                          if isRedirectionTag dcon
                            then do
                              tmp <- dbgTrace (minChatLvl) "Print field_cur: " dbgTrace (minChatLvl) (sdoc (dcur, _field_cur)) dbgTrace (minChatLvl) "End FieldCur\n" gensym "readcursor_indir"
                              tmp_flds <- mapM (\((dcon, idx), _) -> gensym "readcursor_indir_flds") _field_cur
                              loc_var <- lookupVariable loc fenv
                              var_dcon_next <- gensym "dcon_next"
                              vars_next_fields <- mapM (\((dcon, idx), _) -> gensym "field_nxt") _field_cur
                              redirection_var_dcon <- gensym "dcon_redir"
                              res <- mapM (\((dcon, idx), _loc) -> do
                                                                               let locTy = (lookupDataCon ddfs dcon) !! idx
                                                                               case locTy of 
                                                                                                MkTy2 (PackedTy _ loc) -> do
                                                                                                                          let lty = getCursorizeTyFromLocVar Nothing useMutableCursorsCall loc
                                                                                                                          case lty of 
                                                                                                                               CursorTy -> do
                                                                                                                                            new_var <- gensym "fld_redir"
                                                                                                                                            return $ ((dcon, idx), _loc, [new_var])
                                                                                                                               CursorArrayTy _sz -> do  
                                                                                                                                                    num_vars <- mapM (\i -> do 
                                                                                                                                                          var <- gensym "new"
                                                                                                                                                          return var
                                                                                                                                                          ) [1.._sz] 
                                                                                                                                                    return $ ((dcon, idx), _loc, num_vars) 
                                                                                                MkTy2 (CursorArrayTy _sz) -> do
                                                                                                                             num_vars <- mapM (\i -> do 
                                                                                                                                                     var <- gensym "new"
                                                                                                                                                     return var
                                                                                                                                              ) [1.._sz] 
                                                                                                                             return $ ((dcon, idx), _loc, num_vars)
                                                                                                _ -> do 
                                                                                                     new_var <- gensym "fld_redir"
                                                                                                     return $ ((dcon, idx), _loc, [new_var])
                                                                ) _field_cur
                              let redirection_var_flds = concatMap thd3 res
                              -- let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                              -- let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur
                              let tenv' =
                                    M.union
                                      ( M.fromList
                                          [ (tmp, MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                            -- ((loc_var)     , MkTy2 CursorTy),
                                            (redirection_var_dcon, MkTy2 CursorTy),
                                            (toEndV redirection_var_dcon, MkTy2 CursorTy),
                                            (toTagV redirection_var_dcon, MkTy2 IntTy),
                                            (toEndFromTaggedV redirection_var_dcon, MkTy2 CursorTy)
                                          ]
                                      )
                                      tenv
                                  read_cursor =
                                    if isIndirectionTag dcon || isRedirectionTag dcon
                                      then Ext (ReadTaggedCursor var_dcon_next)
                                      else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                                  -- v is the variable i want to send to the call.
                                  -- In this case v is the soa variable where all redirections are unpacked.
                                  binds =
                                    [ (var_dcon_next, [], CursorTy, Ext (AddCursor dcur (LitE 1))),
                                      (tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                      ((loc_var), [], CursorTy, VarE dcur),
                                      (redirection_var_dcon, [], CursorTy, ProjE 0 (VarE tmp)),
                                      (toEndV redirection_var_dcon, [], CursorTy, ProjE 1 (VarE tmp)),
                                      (toTagV redirection_var_dcon, [], IntTy, ProjE 2 (VarE tmp)),
                                      (toEndFromTaggedV redirection_var_dcon, [], CursorTy, Ext $ AddCursor redirection_var_dcon (VarE (toTagV redirection_var_dcon)))
                                    ]

                                  -- generate binds for all fields.
                                  binds_flields =
                                    L.foldl
                                      ( \(index, res) ((dcon', idx), var, redir_vars) ->
                                          let read_cursor_f =
                                                if isIndirectionTag dcon || isRedirectionTag dcon
                                                  then Ext (ReadTaggedCursor (vars_next_fields !! index))
                                                  else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                                              tmpf = tmp_flds !! index
                                              ty_of_field = (lookupDataCon ddfs dcon') !! idx
                                           in case ty_of_field of
                                                (MkTy2 PackedTy {}) ->
                                                  let new_binds = case redir_vars of 
                                                                        [v] -> [(v, [], CursorTy, Ext (AddCursor var (LitE 0)))]
                                                                        rst -> map (\v -> (v, [], CursorTy, Ext (IndexCursorArray var (fromJust $ L.elemIndex v rst)))) rst
                                                   in (index + L.length (redir_vars), res ++ new_binds)
                                                (MkTy2 CursorArrayTy {}) ->
                                                  let new_binds = case redir_vars of 
                                                                        [v] -> [(v, [], CursorTy, Ext (AddCursor var (LitE 0)))]
                                                                        rst -> map (\v -> (v, [], CursorTy, Ext (IndexCursorArray var (fromJust $ L.elemIndex v rst)))) rst
                                                   in (index + L.length (redir_vars), res ++ new_binds)
                                                _ ->
                                                  let new_binds = case redir_vars of 
                                                                        [v] -> 
                                                                                [ (vars_next_fields !! index, [], CursorTy, Ext (AddCursor var (LitE 1))),
                                                                                  (tmpf, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor_f),
                                                                                  -- ((loc_var)     , [], CursorTy, VarE dcur),
                                                                                  ((v), [], CursorTy, ProjE 0 (VarE tmpf)),
                                                                                  (toEndV (v), [], CursorTy, ProjE 1 (VarE tmpf)),
                                                                                  (toTagV (v), [], IntTy, ProjE 2 (VarE tmpf)),
                                                                                  (toEndFromTaggedV (v), [], CursorTy, Ext $ AddCursor (v) (VarE (toTagV (v))))
                                                                                ]
                                                                        _ -> error $ "Did not expect multiple variables for type" ++ show ty_of_field
                                                   in (index + L.length (redir_vars), res ++ new_binds)
                                      )
                                      (0, [])
                                      res
                                  soa_redir_bind = [(v, [], CursorArrayTy (1 + length (redirection_var_flds)), mkMakeCursorArrayDbg v ([redirection_var_dcon] ++ redirection_var_flds))]
                                  tenv'' =
                                    M.union
                                      ( M.fromList
                                          [ (v, MkTy2 $ CursorArrayTy (1 + length (redirection_var_flds)))
                                          ]
                                      )
                                      tenv
                              (bod, m1', m2') <- go m1 m2 curw fenv rst_vlocs rst_tys canBind denv tenv'' -- (toEndV v)
                              return (mkLets (binds ++ (snd binds_flields) ++ soa_redir_bind) bod, m1', m2')
                            else
                              -- This case is different for when the GC is on. 
                              -- Vidush: TODO change this when the GC is on
                              if isIndirectionTag dcon
                                then do
                                   dflags <- getDynFlags
                                   if gopt Opt_DisableGC dflags
                                   then do 
                                    tmp <- gensym "readcursor_indir"
                                    loc_var <- lookupVariable loc fenv
                                    let locs_ty = case (loc) of
                                          FL l -> getCursorizeTyFromLocVar' Nothing useMutableCursorsCall l
                                    let locs_ty3 :: Ty3 = case (loc) of
                                          FL l -> getCursorizeTyFromLocVar Nothing useMutableCursorsCall l
                                    -- let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                                    -- let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur
                                    var_dcon_next <- gensym "dcon_next"
                                    let tenv' =
                                          M.union
                                            ( M.fromList
                                                [ (tmp, MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                                 ((loc_var), locs_ty),
                                                 (v, locs_ty)
                                                 -- (toEndV v, MkTy2 CursorTy),
                                                 -- (toTagV v, MkTy2 IntTy),
                                                 -- (toEndFromTaggedV v, MkTy2 CursorTy)
                                               ]
                                            )
                                            tenv
                                        read_cursor =
                                          if isIndirectionTag dcon || isRedirectionTag dcon
                                            then Ext (ReadTaggedCursor var_dcon_next)
                                            else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                                        mut_loc_pointing_to_dcur = findMutableLocationInSameRegion reg m1
                                        (binds, m1d) = case mut_loc_pointing_to_dcur of 
                                                              Nothing -> ([ (var_dcon_next, [], CursorTy, Ext (AddCursor dcur (LitE 1))),
                                                                            --(tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                                                           (v, [], locs_ty3, Ext $ InitCursor locs_ty3),
                                                                           ("_", [], ProdTy [], Ext (MemCpy v var_dcon_next locs_ty3))
                                                                            -- ,
                                                                            -- (toEndV v, [], CursorTy, ProjE 1 (VarE tmp)),
                                                                            -- (toTagV v, [], IntTy   , ProjE 2 (VarE tmp)),
                                                                            -- End of region needs to be calculated differently
                                                                            -- (toEndFromTaggedV v, [], CursorTy, Ext $ AddCursor v (VarE (toTagV v))),
                                                                            -- ((loc_var), [], locs_ty3, VarE v)
                                                                          ], m1) 
                                                              Just (_, l) -> let 
                                                                          lName = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy l)
                                                                          m1' = updateMutableLocPtsToEnv l m1 (v, Just l, Nothing, S.empty) False
                                                                         in ([ (var_dcon_next, [], CursorTy, Ext (AddCursor dcur (LitE 1))),
                                                                               --(tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                                                               -- (v, [], locs_ty3, Ext $ InitCursor locs_ty3),
                                                                               ("_", [], ProdTy [], Ext (MemCpy lName var_dcon_next locs_ty3))
                                                                               -- ,
                                                                               -- (toEndV v, [], CursorTy, ProjE 1 (VarE tmp)),
                                                                               -- (toTagV v, [], IntTy   , ProjE 2 (VarE tmp)),
                                                                               -- End of region needs to be calculated differently
                                                                               -- (toEndFromTaggedV v, [], CursorTy, Ext $ AddCursor v (VarE (toTagV v))),
                                                                               -- ((loc_var), [], locs_ty3, VarE v)
                                                                          ], m1')
                                        -- binds =
                                        --   [ (var_dcon_next, [], CursorTy, Ext (AddCursor dcur (LitE 1))),
                                        --     --(tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                        --      (v, [], locs_ty3, Ext $ InitCursor locs_ty3),
                                        --      ("_", [], ProdTy [], Ext (MemCpy v var_dcon_next locs_ty3))
                                        --      -- ,
                                        --     -- (toEndV v, [], CursorTy, ProjE 1 (VarE tmp)),
                                        --     -- (toTagV v, [], IntTy   , ProjE 2 (VarE tmp)),
                                        --     -- End of region needs to be calculated differently
                                        --     -- (toEndFromTaggedV v, [], CursorTy, Ext $ AddCursor v (VarE (toTagV v))),
                                        --     -- ((loc_var), [], locs_ty3, VarE v)
                                        --   ]
                                    (bod, m1', m2') <- go m1d m2 curw fenv rst_vlocs rst_tys canBind denv tenv' -- (toEndV v)
                                    return (mkLets binds bod, m1', m2')
                                   else do
                                    let linearizedLocs = case loc of 
                                                              FL l -> linearizeLocVar l
                                    tmp <- dbgTrace (minChatLvl) "Print field_cur: " dbgTrace (minChatLvl) (sdoc (dcur, _field_cur)) dbgTrace (minChatLvl) "End FieldCur\n" gensym "readcursor_indir"
                                    tmp_flds <- mapM (\_ -> gensym "readcursor_indir_flds") linearizedLocs
                                    tmp_unpack <- mapM (\_ -> gensym "tmp_unpack") linearizedLocs
                                    loc_var <- lookupVariable loc fenv
                                    var_dcon_next <- gensym "dcon_next"
                                    vars_next_fields <- mapM (\_ -> gensym "field_nxt") linearizedLocs
                                    redirection_var_dcon <- gensym "dcon_redir"
                                    res <- mapM (\((dcon, idx), _loc) -> do
                                                                               let locTy = (lookupDataCon ddfs dcon) !! idx
                                                                               case locTy of 
                                                                                                MkTy2 (PackedTy _ loc) -> do
                                                                                                                          let lty = getCursorizeTyFromLocVar Nothing useMutableCursorsCall loc
                                                                                                                          case lty of 
                                                                                                                               CursorTy -> do
                                                                                                                                            new_var <- gensym "fld_redir"
                                                                                                                                            return $ ((dcon, idx), _loc, [new_var])
                                                                                                                               CursorArrayTy _sz -> do  
                                                                                                                                                    num_vars <- mapM (\i -> do 
                                                                                                                                                          var <- gensym "new"
                                                                                                                                                          return var
                                                                                                                                                          ) [1.._sz] 
                                                                                                                                                    return $ ((dcon, idx), _loc, num_vars) 
                                                                                                MkTy2 (CursorArrayTy _sz) -> do
                                                                                                                             num_vars <- mapM (\i -> do 
                                                                                                                                                     var <- gensym "new"
                                                                                                                                                     return var
                                                                                                                                              ) [1.._sz] 
                                                                                                                             return $ ((dcon, idx), _loc, num_vars)
                                                                                                _ -> do 
                                                                                                     new_var <- gensym "fld_redir"
                                                                                                     return $ ((dcon, idx), _loc, [new_var])
                                                                ) _field_cur
                                    let redirection_var_flds = concatMap thd3 res
                                    -- let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                                    -- let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur
                                    let tenv' = M.union
                                                ( M.fromList
                                                  [ (tmp, MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                                  -- ((loc_var)     , MkTy2 CursorTy),
                                                    (redirection_var_dcon, MkTy2 CursorTy),
                                                    (toEndV redirection_var_dcon, MkTy2 CursorTy),
                                                    (toTagV redirection_var_dcon, MkTy2 IntTy),
                                                    (toEndFromTaggedV redirection_var_dcon, MkTy2 CursorTy)
                                                  ]
                                                ) tenv
                                        read_cursor =
                                            if isIndirectionTag dcon || isRedirectionTag dcon
                                            then Ext (ReadTaggedCursor var_dcon_next)
                                            else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                                        -- v is the variable i want to send to the call.
                                        -- In this case v is the soa variable where all redirections are unpacked.
                                        mut_loc_pointing_to_dcur = findMutableLocationPointingToVar dcur m1
                                        (binds, m1d) = case mut_loc_pointing_to_dcur of 
                                                                Nothing -> ([ (var_dcon_next, [], CursorTy, Ext (AddCursor dcur (LitE 1))),
                                                                             (tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                                                             ((loc_var), [], CursorTy, VarE dcur),
                                                                             (redirection_var_dcon, [], CursorTy, ProjE 0 (VarE tmp)),
                                                                             (toEndV redirection_var_dcon, [], CursorTy, ProjE 1 (VarE tmp)),
                                                                             (toTagV redirection_var_dcon, [], IntTy, ProjE 2 (VarE tmp)),
                                                                             (toEndFromTaggedV redirection_var_dcon, [], CursorTy, Ext $ AddCursor redirection_var_dcon (VarE (toTagV redirection_var_dcon)))
                                                                            ], m1)
                                                                Just l -> let 
                                                                            lName = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy l)
                                                                            m1' = updateMutableLocPtsToEnv l m1 (redirection_var_dcon, Just l, Nothing, S.empty) False
                                                                          in ([ (var_dcon_next, [], CursorTy, Ext (AddCursor dcur (LitE 1))),
                                                                             (tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                                                             ((loc_var), [], CursorTy, VarE dcur),
                                                                             (redirection_var_dcon, [], CursorTy, ProjE 0 (VarE tmp)),
                                                                             ("_", [], ProdTy [], Ext $ WriteCursorMutable lName (VarE redirection_var_dcon)),
                                                                             (toEndV redirection_var_dcon, [], CursorTy, ProjE 1 (VarE tmp)),
                                                                             (toTagV redirection_var_dcon, [], IntTy, ProjE 2 (VarE tmp)),
                                                                             (toEndFromTaggedV redirection_var_dcon, [], CursorTy, Ext $ AddCursor redirection_var_dcon (VarE (toTagV redirection_var_dcon)))
                                                                            ], m1')
                                        -- generate binds for all fields.
                                        (_, binds_flields, m1', m2') =
                                          L.foldl
                                            ( \(index, res, m1i, m2i) ((dcon', idx), var, redir_vars) ->
                                              let read_cursor_f idx =
                                                      if isIndirectionTag dcon || isRedirectionTag dcon
                                                      then Ext (ReadTaggedCursor (vars_next_fields !! idx))
                                                      else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                                                  tmpf idtmpf = tmp_flds !! idtmpf
                                                  ty_of_field = (lookupDataCon ddfs dcon') !! idx
                                               in case ty_of_field of
                                                    (MkTy2 PackedTy {}) ->
                                                        let (new_binds, m1iout) = case redir_vars of 
                                                                                [v] -> ([ (vars_next_fields !! index, [], CursorTy, Ext (AddCursor var (LitE 1))),
                                                                                        (tmpf index, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor_f index),
                                                                                        -- ((loc_var)     , [], CursorTy, VarE dcur),
                                                                                        ((redirection_var_flds !! index), [], CursorTy, ProjE 0 (VarE $ tmpf index)),
                                                                                        (toEndV (redirection_var_flds !! index), [], CursorTy, ProjE 1 (VarE $ tmpf index)),
                                                                                        (toTagV (redirection_var_flds !! index), [], IntTy, ProjE 2 (VarE $ tmpf index)),
                                                                                        (toEndFromTaggedV (redirection_var_flds !! index), [], CursorTy, Ext $ AddCursor (redirection_var_flds !! index) (VarE (toTagV (redirection_var_flds !! index))))
                                                                                      ], m1i)
                                                                                rst -> (snd $ foldl (\(i, bnds) v -> (i + 1, bnds ++ [ (tmp_unpack !! i, [], CursorTy, Ext (IndexCursorArray var (fromJust $ L.elemIndex v rst))),
                                                                                                    (vars_next_fields !! i, [], CursorTy, Ext (AddCursor (tmp_unpack !! i) (LitE 1))), 
                                                                                                    (tmpf i, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor_f i),
                                                                                                    -- ((loc_var)     , [], CursorTy, VarE dcur),
                                                                                                    ((redirection_var_flds !! i), [], CursorTy, ProjE 0 (VarE $ tmpf i)),
                                                                                                    (toEndV (redirection_var_flds !! i), [], CursorTy, ProjE 1 (VarE $ tmpf i)),
                                                                                                    (toTagV (redirection_var_flds !! i), [], IntTy, ProjE 2 (VarE $ tmpf i)),
                                                                                                    (toEndFromTaggedV (redirection_var_flds !! i), [], CursorTy, Ext $ AddCursor (redirection_var_flds !! i) (VarE (toTagV (redirection_var_flds !! i))))
                                                                                                   ]
                                                                                                   )
                                                                                           ) (index, []) rst, m1i)
                                                         in (index + L.length (redir_vars), res ++ new_binds, m1iout, m2i)
                                                    (MkTy2 CursorArrayTy {}) ->
                                                        let (new_binds, m1iout) = case redir_vars of 
                                                                                [v] -> ([ (vars_next_fields !! index, [], CursorTy, Ext (AddCursor var (LitE 1))),
                                                                                        (tmpf index, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor_f index),
                                                                                        -- ((loc_var)     , [], CursorTy, VarE dcur),
                                                                                        ((redirection_var_flds !! index), [], CursorTy, ProjE 0 (VarE $ tmpf index)),
                                                                                        (toEndV (redirection_var_flds !! index), [], CursorTy, ProjE 1 (VarE $ tmpf index)),
                                                                                        (toTagV (redirection_var_flds !! index), [], IntTy, ProjE 2 (VarE $ tmpf index)),
                                                                                        (toEndFromTaggedV (redirection_var_flds !! index), [], CursorTy, Ext $ AddCursor (redirection_var_flds !! index) (VarE (toTagV (redirection_var_flds !! index))))
                                                                                      ], m1i)
                                                                                -- (v, [], CursorTy, Ext (IndexCursorArray var (fromJust $ L.elemIndex v rst)))
                                                                                rst -> (snd $ foldl (\(i, bnds) v -> (i + 1, bnds ++ [ (tmp_unpack !! i, [], CursorTy, Ext (IndexCursorArray var (fromJust $ L.elemIndex v rst))),
                                                                                                    (vars_next_fields !! i, [], CursorTy, Ext (AddCursor (tmp_unpack !! i) (LitE 1))),
                                                                                                    (tmpf i, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor_f i),
                                                                                                    -- ((loc_var)     , [], CursorTy, VarE dcur),
                                                                                                    ((redirection_var_flds !! i), [], CursorTy, ProjE 0 (VarE $ tmpf i)),
                                                                                                    (toEndV (redirection_var_flds !! i), [], CursorTy, ProjE 1 (VarE $ tmpf i)),
                                                                                                    (toTagV (redirection_var_flds !! i), [], IntTy, ProjE 2 (VarE $ tmpf i)),
                                                                                                    (toEndFromTaggedV (redirection_var_flds !! i), [], CursorTy, Ext $ AddCursor (redirection_var_flds !! i) (VarE (toTagV (redirection_var_flds !! i))))
                                                                                                   ]
                                                                                                   )
                                                                                           ) (index, []) rst, m1i)
                                                         in (index + L.length (redir_vars), res ++ new_binds, m1iout, m2i)
                                                    _ ->
                                                        let (new_binds, m1out) = case redir_vars of 
                                                                                [v] -> let mut_loc_pts_var = findMutableLocationPointingToVar var m1i
                                                                                        in case mut_loc_pts_var of
                                                                                                 Nothing -> let bnds = [ (vars_next_fields !! index, [], CursorTy, Ext (AddCursor var (LitE 1))),
                                                                                                                         (tmpf index, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor_f index),
                                                                                                                         -- ((loc_var)     , [], CursorTy, VarE dcur),
                                                                                                                        ((redirection_var_flds !! index), [], CursorTy, ProjE 0 (VarE $ tmpf index)),
                                                                                                                        (toEndV (redirection_var_flds !! index), [], CursorTy, ProjE 1 (VarE $ tmpf index)),
                                                                                                                        (toTagV (redirection_var_flds !! index), [], IntTy, ProjE 2 (VarE $ tmpf index)),
                                                                                                                        (toEndFromTaggedV (redirection_var_flds !! index), [], CursorTy, Ext $ AddCursor (redirection_var_flds !! index) (VarE (toTagV (redirection_var_flds !! index))))
                                                                                                                       ]
                                                                                                              in (bnds, m1i)
                                                                                                 Just ml -> let m1i' = updateMutableLocPtsToEnv ml m1i ((redirection_var_flds !! index), Just ml, Nothing, S.empty) False
                                                                                                                isFieldAlive = S.member (dcon', idx) aliveBuffersi
                                                                                                                -- write to the mutable location, we need to write the (redirection_var_flds !! index) value.
                                                                                                                mlName = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy ml)
                                                                                                                bnd_write_to_mut_var = if isFieldAlive
                                                                                                                                       then [("_", [], ProdTy [], Ext $ WriteCursorMutable mlName (VarE (redirection_var_flds !! index)))]
                                                                                                                                       else []
                                                                                                                bnds' = [ (vars_next_fields !! index, [], CursorTy, Ext (AddCursor var (LitE 1))),
                                                                                                                          (tmpf index, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor_f index),
                                                                                                                          -- ((loc_var)     , [], CursorTy, VarE dcur),
                                                                                                                          ((redirection_var_flds !! index), [], CursorTy, ProjE 0 (VarE $ tmpf index))] ++ 
                                                                                                                          bnd_write_to_mut_var ++ 
                                                                                                                         [(toEndV (redirection_var_flds !! index), [], CursorTy, ProjE 1 (VarE $ tmpf index)),
                                                                                                                          (toTagV (redirection_var_flds !! index), [], IntTy, ProjE 2 (VarE $ tmpf index)),
                                                                                                                          (toEndFromTaggedV (redirection_var_flds !! index), [], CursorTy, Ext $ AddCursor (redirection_var_flds !! index) (VarE (toTagV (redirection_var_flds !! index))))
                                                                                                                         ]
                                                                                                      in (bnds', m1i') 
                                                                                _ -> error $ "Did not expect multiple variables for ty: " ++ show ty_of_field
                                                         in (index + L.length (redir_vars), res ++ new_binds, m1out, m2i)
                                            ) (0, [], m1d, m2) res
                                        soa_redir_bind = [(v, [], CursorArrayTy (1 + length (redirection_var_flds)), mkMakeCursorArrayDbg v ([redirection_var_dcon] ++ redirection_var_flds))]
                                        mut_loc_in_same_reg = findMutableLocationInSameRegion reg m1'
                                        m1'' = case mut_loc_in_same_reg of 
                                                    Nothing -> m1' 
                                                    Just (_v, lv) -> let m1i = updateMutableLocPtsToEnv lv m1' (v, Just lv, Nothing, S.empty) False
                                                                      in m1i
                                        tenv'' = M.union
                                                ( M.fromList
                                                  [ (v, MkTy2 $ CursorArrayTy (1 + length (redirection_var_flds)))
                                                  ]
                                                ) tenv
                                    (bod, m1''', m2'') <- go m1'' m2' curw fenv rst_vlocs rst_tys canBind denv tenv'' -- (toEndV v)
                                    return (mkLets (binds ++ (binds_flields) ++ soa_redir_bind) bod, m1''', m2'')
                                else error $ "unpackRegularDataCon: cursorty without indirection/redirection."

                        VectorTy el_ty -> do
                          tmp <- gensym "read_vec_tuple"
                          loc_var <- lookupVariable loc fenv
                          let tenv' =
                                M.union
                                  ( M.fromList
                                      [ (tmp, MkTy2 (ProdTy [VectorTy el_ty, CursorTy])),
                                        (v, MkTy2 (VectorTy el_ty)),
                                        (toEndV v, MkTy2 CursorTy)
                                      ]
                                  )
                                  tenv
                              ty' = stripTyLocs ty
                              binds =
                                [ (tmp, [], ProdTy [ty', CursorTy], Ext $ ReadVector (loc_var) (stripTyLocs el_ty)),
                                  (v, [], ty', ProjE 0 (VarE tmp)),
                                  (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))
                                ]
                          let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                          let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur
                          if canBind
                            then do
                              -- If the location exists in the environment, it indicates that the
                              -- corresponding variable was also bound and we shouldn't create duplicate
                              -- bindings (checked in the LetLocE cases).
                              loc_var <- lookupVariable loc fenv
                              let binds' = ((loc_var), [], CursorTy, VarE cur) : binds
                                  tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                              (bod, m1', m2') <- go m1 m2 curw fenv rst_vlocs rst_tys canBind denv tenv'' -- (toEndV v)
                              return (mkLets binds' bod, m1', m2')
                            else do
                              -- Cannot read this int. Instead, we add it to DepEnv.
                              let denv' = M.insertWith (++) (loc) binds denv
                              go m1 m2 curw fenv rst_vlocs rst_tys canBind denv' tenv' -- (toEndV v)
                        ListTy el_ty -> do
                          tmp <- gensym "read_list_tuple"
                          loc_var <- lookupVariable loc fenv
                          let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                          let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur
                          let tenv' =
                                M.union
                                  ( M.fromList
                                      [ (tmp, MkTy2 (ProdTy [ListTy el_ty, CursorTy])),
                                        (v, MkTy2 (ListTy el_ty)),
                                        (toEndV v, MkTy2 CursorTy)
                                      ]
                                  )
                                  tenv
                              ty' = stripTyLocs ty
                              binds =
                                [ (tmp, [], ProdTy [ty', CursorTy], Ext $ ReadList (loc_var) (stripTyLocs el_ty)),
                                  (v, [], ty', ProjE 0 (VarE tmp)),
                                  (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))
                                ]
                          if canBind
                            then do
                              -- If the location exists in the environment, it indicates that the
                              -- corresponding variable was also bound and we shouldn't create duplicate
                              -- bindings (checked in the LetLocE cases).
                              loc_var <- lookupVariable loc fenv
                              let binds' = ((loc_var), [], CursorTy, VarE cur) : binds
                                  tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'
                              (bod, m1', m2') <- go m1 m2 curw fenv rst_vlocs rst_tys canBind denv tenv'' -- (toEndV v)
                              return (mkLets binds' bod, m1', m2')
                            else do
                              -- Cannot read this int. Instead, we add it to DepEnv.
                              let denv' = M.insertWith (++) (loc) binds denv
                              go m1 m2 curw fenv rst_vlocs rst_tys canBind denv' tenv' -- (toEndV v)
                        PackedTy tycon ploc -> do
                          -- Two cases
                          -- If the PackedTy is the same tycon then
                          -- If the PackedTy is not the same tycon
                          let datacons = getConOrdering ddfs tycon
                          let isSameTycon = if (elem dcon datacons) then True else False
                          case isSameTycon of
                            True -> do
                              let ty3_of_field = getCursorizeTyFromLocVar' Nothing useMutableCursorsCall ploc
                              let ty3_of_field2 :: Ty3 = getCursorizeTyFromLocVar Nothing useMutableCursorsCall ploc
                              let tenv' = M.insert v ( ty3_of_field) tenv
                              let field_idx = lookupFieldIdx (v, locarg)
                              -- let cur = fromJust $ L.lookup (dcon, field_idx) field_cur
                              let cur = dcur
                              loc_var <- lookupVariable loc fenv
                              if canBind
                                then do
                                  let tenv'' = M.insert (loc_var) ( ty3_of_field) tenv'
                                  -- Flip canBind to indicate that the subsequent fields
                                  -- should be added to the dependency environment.
                                  dcon_next <- gensym $ toVar $ (fromVar dcur) ++ "_next"
                                  -- Vidush: TODO: things need to change here since the type in Cursorize Ty needs to change
                                  end_fields <- mapM (\((dcon, idx), _loc) ->  do
                                                                                let locTy = (lookupDataCon ddfs dcon) !! idx
                                                                                case locTy of 
                                                                                      MkTy2 (PackedTy _ loc) -> do
                                                                                                                let lty = getCursorizeTyFromLocVar Nothing useMutableCursorsCall loc
                                                                                                                case lty of 
                                                                                                                   CursorTy -> do
                                                                                                                                 return $ ((dcon, idx), _loc, ([], [_loc]))
                                                                                                                   CursorArrayTy _sz -> do  
                                                                                                                                        num_vars <- mapM (\i -> do 
                                                                                                                                                           var <- gensym "new"
                                                                                                                                                           return var
                                                                                                                                                         ) [1.._sz] 
                                                                                                                                        let bnds = map (\v -> (v, [], CursorTy, Ext (IndexCursorArray _loc (fromJust $ L.elemIndex v num_vars)))) num_vars
                                                                                                                                        return $ ((dcon, idx), _loc, (bnds, num_vars)) 
                                                                                      MkTy2 (CursorArrayTy _sz) -> do
                                                                                                                   num_vars <- mapM (\i -> do 
                                                                                                                                            var <- gensym "new"
                                                                                                                                            return var
                                                                                                                                    ) [1.._sz] 
                                                                                                                   let bnds = map (\v -> (v, [], CursorTy, Ext (IndexCursorArray _loc (fromJust $ L.elemIndex v num_vars)))) num_vars
                                                                                                                   return $ ((dcon, idx), _loc, (bnds, num_vars))
                                                                                      _ -> do
                                                                                            return $ ((dcon, idx), _loc, ([], [_loc]))
                                                       ) _field_cur
                                  let end_fields_tmp = map thd3 end_fields
                                  let end_fields' = concatMap snd end_fields_tmp
                                  let end_fields_bnds = concatMap fst end_fields_tmp
                                  -- Vidush: Will need to track the input mutable locations here
                                  -- Logic for tracking mutable locations in SoA paradigm needs to fixing.
                                  let makeCurArr = mkMakeCursorArrayDbg loc_var ([dcon_next] ++ end_fields')
                                  let let_mk_cur_arr = (loc_var, [], CursorArrayTy (1 + length (end_fields')), makeCurArr)
                                  let dcon_nxt = [(dcon_next, [], CursorTy, Ext $ AddCursor dcur (LitE 1))] ++ end_fields_bnds ++ [let_mk_cur_arr, (v, [], CursorArrayTy (1 + length (end_fields')), VarE (loc_var))]
                                  let mutLocInSameRegion = findMutableLocationInSameRegion reg m1
                                  -- update the env that points to the mutable loc
                                  let m1' = case mutLocInSameRegion of 
                                                      Nothing -> m1
                                                      Just (var, mloc) -> dbgTrace (minChatLvl) "Print mloc in same region: " dbgTrace (minChatLvl) (sdoc (v, reg, var, mloc, m1, loc_var)) dbgTrace (minChatLvl) "End mloc in same region!\n" updateMutableLocPtsToEnv mloc m1 (v, Just mloc, Just reg, S.empty) False
                                  -- make the new curw type
                                  -- this consists of incrementing the data constructor buffer by one and all the rest of the fields
                                  let curw' = SoAWin dcon_next _field_cur
                                  (bod, m1', m2') <- go m1' m2 curw' fenv rst_vlocs rst_tys False denv tenv'' -- (toEndV v)
                                  dbgTrace (minChatLvl) "Print in PackedTy unpacked Dcon: " dbgTrace (minChatLvl) (sdoc (loc, v, m1')) dbgTrace (minChatLvl) "End print in packedTy SoA Case.\n" return (mkLets dcon_nxt bod, m1', m2')
                                else do
                                  -- Cannot read this. Instead, we add it to DepEnv.
                                  let delayedPackedRhs = case ty3_of_field2 of
                                        CursorTy -> cursorValueFromMaybeTrackedMut m1 tenv loc_var
                                        _ -> VarE loc_var
                                  let denv' = M.insertWith (++) (loc) [(v, [], ty3_of_field2, delayedPackedRhs)] denv
                                  dbgTrace (minChatLvl) "Print in PackedTy unpacked Dcon: " dbgTrace (minChatLvl) (sdoc (loc, v, loc_var)) dbgTrace (minChatLvl) "End print in packedTy SoA cannot bind Case.\n" go m1 m2 curw fenv rst_vlocs rst_tys False denv' tenv' -- (toEndV v)
                            False -> do
                              let ty3_of_field = getCursorizeTyFromLocVar' Nothing useMutableCursorsCall ploc
                              let ty3_of_field2 :: Ty3 = getCursorizeTyFromLocVar Nothing useMutableCursorsCall ploc
                              let tenv' = M.insert v (ty3_of_field) tenv
                              let field_idx = lookupFieldIdx (v, locarg)
                              let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur
                              -- let cur = dcur
                              loc_var <- lookupVariable loc fenv
                              if canBind
                                then do
                                  let tenv'' = M.insert (loc_var) ( ty3_of_field) tenv'
                                  -- Flip canBind to indicate that the subsequent fields
                                  -- should be added to the dependency environment.
                                  (bod, m1', m2') <- go m1 m2 curw fenv rst_vlocs rst_tys False denv tenv'' -- (toEndV v)
                                  return (
                                    mkLets
                                      [ ((loc_var), [], ty3_of_field2, VarE cur),
                                        (v, [], ty3_of_field2, VarE (loc_var))
                                      ]
                                      bod, m1', m2')
                                else do
                                  -- Cannot read this. Instead, we add it to DepEnv.
                                  let delayedLocRhs = case ty3_of_field2 of
                                        CursorTy -> cursorValueFromMaybeTrackedMut m1 tenv cur
                                        _ -> VarE cur
                                  let delayedPackedRhs = case ty3_of_field2 of
                                        CursorTy -> cursorValueFromMaybeTrackedMut m1 tenv loc_var
                                        _ -> VarE loc_var
                                  let denvBase = M.insertWith (++) (loc) [((loc_var), [], ty3_of_field2, delayedLocRhs), (v, [], ty3_of_field2, delayedPackedRhs)] denv
                                  let denv' = dbgTrace (minChatLvl) "Printing in packedTy unpack dcon: " dbgTrace (minChatLvl) (sdoc (loc)) dbgTrace (minChatLvl) "End in unpacking dcon.\n" denvBase
                                  (bod, m1', m2') <- go m1 m2 curw fenv rst_vlocs rst_tys False denv' tenv' -- (toEndV v)
                                  -- VS: [05.11.2025] This is a hack to ensure that the location variable is not undefined.
                                  -- If we have serialized packed types that are not self recursive, we still have to release
                                  -- The let binding and just adding it to the depenv is not enough.
                                  -- There should be a careful look at why this is and if this is functionally correct.
                                  return (
                                    mkLets
                                      [((loc_var), [], ty3_of_field2, VarE cur), (v, [], ty3_of_field2, VarE (loc_var))]
                                      bod, m1', m2')
                        _ -> error $ "unpackRegularDataCon: Unexpected field " ++ sdoc (v, loc) ++ ":" ++ sdoc ty
                _ -> error $ "unpackRegularDataCon: Unexpected numnber of varible, type pairs: " ++ show (vlocs, tys)

    -- We have access to all fields in this constructor, and can create
    -- bindings for everything. We begin by unpacking the random access nodes.
    unpackWithAbsRAN :: M.Map Var Ty2 -> S.Set (DataCon, Int) -> MutableLocPtsToEnv -> MutableLocOldValueEnv -> WindowIntoCursor -> M.Map FreeVarsTy Var -> PassM Exp3
    unpackWithAbsRAN tenvarg alive_buffers m1 m2 field_cur freeVarToVarEnv_unpack =
      -- A map from a variable to a tuple containing it's location and
      -- the RAN field it depends on. Consider this constructor:
      --
      --     (Node^ [(ran_y3, loc_ran_y3), (n1, loc_n1) , (x2 , loc_x2), (y3 , loc_y3)] ...),
      --
      -- it will be the map:
      --
      --     (y3 -> (loc_y3, ran_y3))
      let ran_mp =
            case numRANsDataCon (M.map (fmap unTy2) ddfs) (fromRANDataCon dcon) of
              0 -> M.empty
              n ->
                let -- Random access nodes occur immediately after the tag
                    ind_vars = L.map fst $ L.take n vlocs1
                    -- Everything else is a regular consturctor field,
                    -- which depends on some random access node
                    data_fields = reverse $ L.take n (reverse vlocs1)
                    (vars, var_locargs) = unzip data_fields
                    var_locs = map (unwrapLocVar . toLocVar) var_locargs
                 in M.fromList $ zip vars (zip var_locs ind_vars)
          -- tenvarg' = case field_cur of
          --   AoSWin cf -> (M.insert cf (MkTy2 CursorTy) tenvarg)
          --   SoAWin dcf fieldfvs ->
          --     let tenv1'' = M.insert dcf (MkTy2 CursorTy) tenvarg
          --      in -- VS: TODO: This is assuming that each field is cursorTy
          --         -- we should change this OR we can reply on addCasts to fix casting??
          --         foldr (\(x, y) acc -> if M.member y acc
          --                               then acc 
          --                               else M.insert y (MkTy2 CursorTy) acc
          --               ) tenv1'' fieldfvs
       in go True m1 m2 field_cur freeVarToVarEnv_unpack vlocs1 tys1 ran_mp denv1 tenvarg
      where
        go :: Bool -> MutableLocPtsToEnv -> MutableLocOldValueEnv -> WindowIntoCursor -> M.Map FreeVarsTy Var -> [(Var, LocArg)] -> [Ty2] -> M.Map Var (Var, Var) -> DepEnv -> TyEnv Var Ty2 -> PassM Exp3
        go isFirstPacked m1g m2g curw fenv vlocs tys indirections_env denv tenvgoarg = do
          case curw of
            AoSWin cur -> do
              case (vlocs, tys) of
                ([], []) -> do 
                             (exp, _, _) <- processRhs m1g m2g fenv denv tenvgoarg
                             return exp
                ((v, locarg) : rst_vlocs, (MkTy2 ty) : rst_tys) ->
                  let loc = fromLocArgToFreeVarsTy locarg
                   in case ty of
                        -- The random access pointer
                        -- ASSUMPTION: We can always bind it, since it occurs immediately after the tag.
                        {-
                            CursorTy -> do
                               tmp <- gensym "readcursor_shortcut"
                               let tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [CursorTy, CursorTy])),
                                                               (loc     , MkTy2 CursorTy),
                                                               (v       , MkTy2 CursorTy),
                                                               (toEndV v, MkTy2 CursorTy)])
                                            tenv

                                   binds = [(tmp     , [], ProdTy [CursorTy, CursorTy], Ext $ ReadCursor cur),
                                            (loc     , [], CursorTy, VarE cur),
                                            (v       , [], CursorTy, ProjE 0 (VarE tmp)),
                                            (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                                   bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv'
                                   return $ mkLets binds bod
                        -}

                        CursorTy -> do
                          -- TODO: We need to handle shortcut pointers in case of mutable location.
                          tmp <- gensym "readcursor_shortcut"
                          locs_var <- lookupVariable loc fenv
                          let tenv' =
                                M.union
                                  ( M.fromList
                                      [ (tmp, MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                        (locs_var, MkTy2 CursorTy),
                                        (v, MkTy2 CursorTy),
                                        (toEndV v, MkTy2 CursorTy),
                                        (toTagV v, MkTy2 IntTy),
                                        (toEndFromTaggedV v, MkTy2 CursorTy)
                                      ]
                                  )
                                  tenvgoarg
                              read_cursor = Ext (ReadTaggedCursor cur)
                              binds =
                                [ (tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                  (locs_var, [], CursorTy, VarE cur),
                                  (v, [], CursorTy, ProjE 0 (VarE tmp)),
                                  (toEndV v, [], CursorTy, ProjE 1 (VarE tmp)),
                                  (toTagV v, [], IntTy, ProjE 2 (VarE tmp)),
                                  (toEndFromTaggedV v, [], CursorTy, Ext $ AddCursor v (VarE (toTagV v)))
                                ]
                          let checkMutLoc = findMutableLocationPointingToVar cur m1g 
                          (m1g', add_bnds) <- case checkMutLoc of 
                                          Nothing -> dbgTrace (minChatLvl) "Print in unpack abs ran Cursor, Nothing case: " dbgTrace (minChatLvl) (sdoc (cur)) dbgTrace (minChatLvl) "End in unpack abs ran Cursor Nothing case.\n" return (m1g, []) 
                                          Just ml -> do
                                                     let m1inner = updateMutableLocPtsToEnv ml m1g (toEndV v, Just ml, Nothing, S.empty) False
                                                     void_var <- gensym "void"
                                                     let mlName = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy ml)
                                                     -- Vidush: perhaps better to get the size from the type rather than hardcode the size of 8 here. ? 
                                                     let bnd = [(void_var, [], ProdTy [], Ext $ BumpCursorMutable mlName (LitE 8))]
                                                     dbgTrace (minChatLvl) "Print in unpack abs ran Cursor, Just l case: " dbgTrace (minChatLvl) (sdoc (cur, ml)) dbgTrace (minChatLvl) "End in unpack abs ran Cursor Just l case.\n" return (m1inner, bnd)
                          bod <- go isFirstPacked m1g' m2g (AoSWin (toEndV v)) fenv rst_vlocs rst_tys indirections_env denv tenv'
                          return $ mkLets (binds ++ add_bnds)  bod

                        -- Int, Sym, or Bool
                        _ | isScalarTy ty -> do
                          locs_var <- lookupVariable loc fenv
                          let mut_loc = findMutableLocationPointingToVar cur m1g
                          m1' <- case mut_loc of
                                            Nothing -> dbgTrace (minChatLvl) "Print in unpack abs ran Scalar, Nothing case: " dbgTrace (minChatLvl) (sdoc (cur)) dbgTrace (minChatLvl) "End in unpack abs ran Scalar Nothing case.\n" return m1g
                                            Just l -> do
                                                       let m1inner = updateMutableLocPtsToEnv l m1g (locs_var, Just l, Nothing, S.singleton cur) True
                                                       dbgTrace (minChatLvl) "Print in unpack abs ran Scalar, Just l case: " dbgTrace (minChatLvl) (sdoc (cur, l)) dbgTrace (minChatLvl) "End in unpack abs ran Scalar Just l case.\n" return m1inner
                          (tenv', binds, m1'', m2') <- scalarBinds True fenv m1' m2 ty v locs_var locarg tenvgoarg
                          let loc_bind = case M.lookup v indirections_env of
                                Nothing ->
                                  (locs_var, [], CursorTy, VarE cur)
                                -- Read this using a random access node
                                Just (_var_loc, ind_var) ->
                                  (locs_var, [], CursorTy, VarE ind_var)
                              binds' = loc_bind : binds
                              tenv'' = M.insert locs_var (MkTy2 CursorTy) tenv'
                          bod <- go isFirstPacked m1'' m2' (AoSWin (toEndV v)) fenv rst_vlocs rst_tys indirections_env denv tenv''
                          return $ mkLets binds' bod

                        VectorTy el_ty -> do
                          locs_var <- lookupVariable loc fenv
                          tmp <- gensym "read_vec_tuple"
                          let tenv' =
                                M.union
                                  ( M.fromList
                                      [ (tmp, MkTy2 (ProdTy [VectorTy el_ty, CursorTy])),
                                        (v, MkTy2 (VectorTy el_ty)),
                                        (toEndV v, MkTy2 CursorTy)
                                      ]
                                  )
                                  tenvgoarg
                              ty' = stripTyLocs ty
                              binds =
                                [ (tmp, [], ProdTy [ty', CursorTy], Ext $ ReadVector locs_var (stripTyLocs el_ty)),
                                  (v, [], ty', ProjE 0 (VarE tmp)),
                                  (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))
                                ]
                              loc_bind = case M.lookup v indirections_env of
                                Nothing ->
                                  (locs_var, [], CursorTy, VarE cur)
                                Just (_var_loc, ind_var) ->
                                  (locs_var, [], CursorTy, VarE ind_var)
                              binds' = loc_bind : binds
                              tenv'' = M.insert locs_var (MkTy2 CursorTy) tenv'
                          bod <- go isFirstPacked m1g m2g (AoSWin (toEndV v)) fenv rst_vlocs rst_tys indirections_env denv tenv''
                          return $ mkLets binds' bod

                        ListTy el_ty -> do
                          locs_var <- lookupVariable loc fenv
                          tmp <- gensym "read_list_tuple"
                          let tenv' =
                                M.union
                                  ( M.fromList
                                      [ (tmp, MkTy2 (ProdTy [VectorTy el_ty, CursorTy])),
                                        (v, MkTy2 (ListTy el_ty)),
                                        (toEndV v, MkTy2 CursorTy)
                                      ]
                                  )
                                  tenvgoarg
                              ty' = stripTyLocs ty
                              binds =
                                [ (tmp, [], ProdTy [ty', CursorTy], Ext $ ReadList locs_var (stripTyLocs el_ty)),
                                  (v, [], ty', ProjE 0 (VarE tmp)),
                                  (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))
                                ]
                              loc_bind = case M.lookup v indirections_env of
                                Nothing ->
                                  (locs_var, [], CursorTy, VarE cur)
                                Just (_var_loc, ind_var) ->
                                  (locs_var, [], CursorTy, VarE ind_var)
                              binds' = loc_bind : binds
                              tenv'' = M.insert locs_var (MkTy2 CursorTy) tenv'
                          bod <- go isFirstPacked m1g m2g (AoSWin (toEndV v)) fenv rst_vlocs rst_tys indirections_env denv tenv''
                          return $ mkLets binds' bod

                        PackedTy {} -> do
                          locs_var <- lookupVariable loc fenv
                          let tenv' =
                                M.union
                                  ( M.fromList
                                      [ (locs_var, MkTy2 CursorTy),
                                        (v, MkTy2 CursorTy)
                                      ]
                                  )
                                  tenvgoarg
                              (loc_bind, var_used) = case M.lookup v indirections_env of
                                -- This is the first packed value. We can unpack this.
                                Nothing ->
                                  ((locs_var, [], CursorTy, VarE cur), cur)
                                -- We need to access this using a random access node
                                Just (_var_loc, ind_var) ->
                                  ((locs_var, [], CursorTy, VarE ind_var), ind_var)
                          let mut_var = findMutableLocationPointingToVar cur m1g
                          -- Vidush: For now this breaks,
                          -- I think to really fix the code here, the mutable loc env shoud be keyed by 
                          -- var or, (loc,var) to keep the current code functionining.
                          (m1g', addl_bnds, isFirstPacked') <- case mut_var of 
                                                  Nothing -> dbgTrace (minChatLvl) "Print in unpackWithRelDataCon: " dbgTrace (minChatLvl) (sdoc (cur)) dbgTrace (minChatLvl) "End in unpackWithRelDataCon NOTHING.\n" return (m1g, [], isFirstPacked) 
                                                  Just ml -> do
                                                             if (isLocAlive (getLocVarFromFreeVarsTy loc) rhs False) && isFirstPacked
                                                             then do 
                                                              let m1inner = updateMutableLocPtsToEnv ml m1g ((toEndV v), Just ml, Nothing, S.fromList [v, locs_var, var_used]) True
                                                              void <- gensym "void"
                                                              let mlname = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy ml)
                                                              let bump_bnd = [(void, [], ProdTy [], Ext $ WriteCursorMutable mlname (VarE var_used))]
                                                              dbgTrace (minChatLvl) "Print in unpackWithRelDataCon: " dbgTrace (minChatLvl) (sdoc (cur)) dbgTrace (minChatLvl) "End in unpackWithRelDataCon IF.\n" pure (m1inner, bump_bnd, False)
                                                             else do
                                                                let m1inner = updateMutableLocPtsToEnv ml m1g ((toEndV v), Just ml, Nothing, S.fromList [v, locs_var, var_used]) True
                                                                dbgTrace (minChatLvl) "Print in unpackWithRelDataCon: " dbgTrace (minChatLvl) (sdoc (cur)) dbgTrace (minChatLvl) "End in unpackWithRelDataCon ELSE.\n" pure (m1inner, [], True)
                                                              
                          bod <- go isFirstPacked' m1g' m2g (AoSWin (toEndV v)) fenv rst_vlocs rst_tys indirections_env denv tenv'
                          return $ mkLets ([loc_bind, (v, [], CursorTy, VarE locs_var)] ++ addl_bnds) bod

                        _ -> error $ "unpackWitnAbsRAN: Unexpected field " ++ sdoc (v, loc) ++ ":" ++ sdoc ty

                _ -> error $ "unpackWitnAbsRAN: Unexpected numnber of varible, type pairs: " ++ show (vlocs, tys)
            SoAWin dcur_end _field_cur -> do
              case (vlocs, tys) of
                ([], []) -> do 
                             (exp, _, _) <- processRhs m1 m2 fenv denv tenvgoarg
                             return exp
                ((v, locarg) : rst_vlocs, (MkTy2 ty) : rst_tys) ->
                  let loc = fromLocArgToFreeVarsTy locarg
                   in case ty of
                        -- The random access pointer
                        -- ASSUMPTION: We can always bind it, since it occurs immediately after the tag.
                        {-
                            CursorTy -> do
                               tmp <- gensym "readcursor_shortcut"
                               let tenv' = M.union (M.fromList [(tmp     , MkTy2 (ProdTy [CursorTy, CursorTy])),
                                                               (loc     , MkTy2 CursorTy),
                                                               (v       , MkTy2 CursorTy),
                                                               (toEndV v, MkTy2 CursorTy)])
                                            tenv

                                   binds = [(tmp     , [], ProdTy [CursorTy, CursorTy], Ext $ ReadCursor cur),
                                            (loc     , [], CursorTy, VarE cur),
                                            (v       , [], CursorTy, ProjE 0 (VarE tmp)),
                                            (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                                   bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv'
                                   return $ mkLets binds bod
                        -}

                        CursorTy -> do
                          tmp <- gensym "readcursor_shortcut"
                          locs_var <- lookupVariable loc fenv
                          let tenv' =
                                M.union
                                  ( M.fromList
                                      [ (tmp, MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                        (locs_var, MkTy2 CursorTy),
                                        (v, MkTy2 CursorTy),
                                        (toEndV v, MkTy2 CursorTy),
                                        (toTagV v, MkTy2 IntTy),
                                        (toEndFromTaggedV v, MkTy2 CursorTy)
                                      ]
                                  )
                                  tenvgoarg
                              read_cursor = Ext (ReadTaggedCursor dcur_end)
                              binds =
                                [ (tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                                  (locs_var, [], CursorTy, VarE dcur_end),
                                  (v, [], CursorTy, ProjE 0 (VarE tmp)),
                                  (toEndV v, [], CursorTy, ProjE 1 (VarE tmp)),
                                  (toTagV v, [], IntTy, ProjE 2 (VarE tmp)),
                                  (toEndFromTaggedV v, [], CursorTy, Ext $ AddCursor v (VarE (toTagV v)))
                                ]
                          let curw' = SoAWin (toEndV v) _field_cur 
                          bod <- go isFirstPacked m1g m2g curw' fenv rst_vlocs rst_tys indirections_env denv tenv'
                          return $ mkLets binds bod

                        CursorArrayTy sz -> do
                          tmp <- gensym "readcursor_shortcut"
                          locs_var <- lookupVariable loc fenv
                          let tenv' =
                                M.union
                                  ( M.fromList
                                      [ (tmp, MkTy2 (ProdTy [CursorTy, CursorTy, IntTy])),
                                        (locs_var, MkTy2 (CursorArrayTy sz)),
                                        (v, MkTy2 (CursorArrayTy sz)),
                                        (toEndV v, MkTy2 CursorTy),
                                        (toTagV v, MkTy2 IntTy),
                                        (toEndFromTaggedV v, MkTy2 CursorTy)
                                      ]
                                  )
                                  tenvgoarg
                              --dcur_end is where i want to read the shortcut pointer from
                              -- we'd just do a memcpy and copy the random access pointer out
                              --read_cursor = Ext (ReadTaggedCursor dcur_end)
                              --binds =
                              --  [ (tmp, [], ProdTy [CursorTy, CursorTy, IntTy], read_cursor),
                              --    (locs_var, [], CursorTy, VarE dcur_end),
                              --    (v, [], CursorTy, ProjE 0 (VarE tmp)),
                              --    (toEndV v, [], CursorTy, ProjE 1 (VarE tmp)),
                              --    (toTagV v, [], IntTy, ProjE 2 (VarE tmp)),
                              --    (toEndFromTaggedV v, [], CursorTy, Ext $ AddCursor v (VarE (toTagV v)))
                              --  ]
                              binds = [  
                                        (v, [], (CursorArrayTy sz), Ext $ InitCursor (CursorArrayTy sz)),
                                        --(locs_var, [], (CursorArrayTy sz), VarE dcur_end),
                                        ("_", [], ProdTy [], Ext (MemCpy v dcur_end (CursorArrayTy sz))),
                                        (toEndV v, [], CursorTy, Ext $ AddCursor dcur_end (LitE (8 * sz)))
                                      ]
                          let curw' = SoAWin (toEndV v) _field_cur 
                          bod <- go isFirstPacked m1g m2g curw' fenv rst_vlocs rst_tys indirections_env denv tenv'
                          return $ mkLets binds bod


                        -- Int, Sym, or Bool
                        _ | isScalarTy ty -> do
                          locs_var <- lookupVariable loc fenv
                          (tenv', binds, m1', m2') <- scalarBinds True fenv m1g m2g ty v locs_var locarg tenvgoarg
                          let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                          let field_cur' = map (\(k@(d, idx), var) -> if (d, idx) == (dcon, field_idx) then (k, (toEndV v)) else (k, var)) _field_cur
                          let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur
                          let loc_bind = case M.lookup v indirections_env of
                                -- cannot follow indirection, field
                                Nothing ->
                                  (locs_var, [], CursorTy, VarE cur)
                                -- Read this using a random access node
                                Just (_var_loc, ind_var) ->
                                  (locs_var, [], CursorTy, VarE ind_var)
                              binds' = loc_bind : binds
                              tenv'' = dbgTrace (minChatLvl) "Print in scalar ty: " dbgTrace (minChatLvl) (sdoc (loc_bind)) dbgTrace (minChatLvl) "End in scalar ty SoA unpackDcon!\n." M.insert locs_var (MkTy2 CursorTy) tenv'
                          bod <- go isFirstPacked m1' m2' (SoAWin dcur_end field_cur') fenv rst_vlocs rst_tys indirections_env denv tenv''
                          return $ mkLets binds' bod

                        -- _ | isScalarTy ty -> do
                        --   loc_var <- lookupVariable loc fenv
                        --   (tenv', binds) <- scalarBinds ty v loc_var tenv
                        --   let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                        --   let field_cur' = map (\(k@(d, idx), var) -> if (d, idx) == (dcon, field_idx) then (k, (toEndV v)) else (k, var)) _field_cur
                        --   let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur
                        --   if canBind
                        --     then do
                        --       -- If the location exists in the environment, it indicates that the
                        --       -- corresponding variable was also bound and we shouldn't create duplicate
                        --       -- bindings (checked in the LetLocE cases).
                        --       loc_var <- lookupVariable loc fenv
                        --       let binds' = ((loc_var), [], CursorTy, VarE cur) : binds
                        --           tenv'' = M.insert (loc_var) (MkTy2 CursorTy) tenv'

                        --       bod <- go (SoAWin dcur field_cur') fenv rst_vlocs rst_tys canBind denv tenv''
                        --       return $ mkLets binds' bod
                        --     else do
                        --       -- Cannot read this int. Instead, we add it to DepEnv.
                        --       let denv' = M.insertWith (++) (loc) binds denv
                        --       go (SoAWin dcur field_cur') fenv rst_vlocs rst_tys canBind denv' tenv'



                        -- VS: TODO, needs to change for SOA 
                        -- VectorTy el_ty -> do
                        --   tmp <- gensym "read_vec_tuple"
                        --   let tenv' =
                        --         M.union
                        --           ( M.fromList
                        --               [ (tmp, MkTy2 (ProdTy [VectorTy el_ty, CursorTy])),
                        --                 (v, MkTy2 (VectorTy el_ty)),
                        --                 (toEndV v, MkTy2 CursorTy)
                        --               ]
                        --           )
                        --           tenv
                        --       ty' = stripTyLocs ty
                        --       binds =
                        --         [ (tmp, [], ProdTy [ty', CursorTy], Ext $ ReadVector locs_var (stripTyLocs el_ty)),
                        --           (v, [], ty', ProjE 0 (VarE tmp)),
                        --           (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))
                        --         ]
                        --       loc_bind = case M.lookup v indirections_env of
                        --         Nothing ->
                        --           (locs_var, [], CursorTy, VarE dcur_end)
                        --         Just (_var_loc, ind_var) ->
                        --           (locs_var, [], CursorTy, VarE ind_var)
                        --       binds' = loc_bind : binds
                        --       tenv'' = M.insert locs_var (MkTy2 CursorTy) tenv'
                        --   bod <- go curw fenv rst_vlocs rst_tys indirections_env denv tenv''
                        --   return $ mkLets binds' bod
                       
                        -- ListTy el_ty -> do
                        --   tmp <- gensym "read_list_tuple"
                        --   let tenv' =
                        --         M.union
                        --           ( M.fromList
                        --               [ (tmp, MkTy2 (ProdTy [VectorTy el_ty, CursorTy])),
                        --                 (v, MkTy2 (ListTy el_ty)),
                        --                 (toEndV v, MkTy2 CursorTy)
                        --               ]
                        --           )
                        --           tenv
                        --       ty' = stripTyLocs ty
                        --       binds =
                        --         [ (tmp, [], ProdTy [ty', CursorTy], Ext $ ReadList locs_var (stripTyLocs el_ty)),
                        --           (v, [], ty', ProjE 0 (VarE tmp)),
                        --           (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))
                        --         ]
                        --       loc_bind = case M.lookup v indirections_env of
                        --         Nothing ->
                        --           (locs_var, [], CursorTy, VarE dcur_end)
                        --         Just (_var_loc, ind_var) ->
                        --           (locs_var, [], CursorTy, VarE ind_var)
                        --       binds' = loc_bind : binds
                        --       tenv'' = M.insert locs_var (MkTy2 CursorTy) tenv'
                        --   bod <- go curw fenv rst_vlocs rst_tys indirections_env denv tenv''
                        --   return $ mkLets binds' bod



                        PackedTy tycon ploc -> do
                          -- Two cases 
                          -- If the packedty is the same tycon, ie, recursive.
                          -- otherwise if its not the same tycon but another packed field
                          let datacons = getConOrdering ddfs tycon
                          let isSameTycon = if (elem dcon datacons) then True else False
                          locs_var <- lookupVariable loc fenv
                          case isSameTycon of
                                -- recursive part
                                -- availabe in data con buffer
                                -- we could also take ran pointer to it
                                True -> do
                                         let ty3_of_field = getCursorizeTyFromLocVar' Nothing useMutableCursorsCall ploc
                                         let ty3_of_field2 :: Ty3 = getCursorizeTyFromLocVar Nothing useMutableCursorsCall ploc
                                        
                                         let tenv' = M.insert v (ty3_of_field) tenvgoarg
                                         let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                                         let cur = dcur_end
                                         let tenv'' =
                                              M.union
                                                ( M.fromList
                                                    [ (locs_var,  ty3_of_field),
                                                      (v,  ty3_of_field)
                                                    ]
                                                )
                                                tenv'
                                         
                                         case M.lookup v indirections_env of
                                              -- This is the first packed value. We can unpack this.
                                              Nothing -> do 
                                                 dcon_next <- gensym $ toVar $ (fromVar cur) ++ "_next"
                                                 let end_fields = map (\(key, varr) -> varr) _field_cur
                                                 let makeCurArr = mkMakeCursorArrayDbg locs_var ([dcon_next] ++ end_fields)
                                                 let let_mk_cur_arr = (locs_var, [], ty3_of_field2, makeCurArr)
                                                 let dcon_nxt = [(dcon_next, [], CursorTy, VarE cur)] ++ [let_mk_cur_arr, (v, [], ty3_of_field2, VarE (locs_var))]
                                                 let curw' = SoAWin dcon_next _field_cur
                                                 bod <- go isFirstPacked m1g m2g curw' fenv rst_vlocs rst_tys indirections_env denv tenv'
                                                 return $ mkLets dcon_nxt bod
                                              -- We need to access this using a random access node
                                              Just (_var_loc, ind_var) -> do
                                                dcon_next <- gensym $ toVar $ (fromVar cur) ++ "_next"
                                                let end_fields = map (\(key, varr) -> varr) _field_cur
                                                let bnd = (locs_var, [], ty3_of_field2, VarE ind_var)
                                                let dcon_nxt = [(dcon_next, [], CursorTy, VarE cur)] ++ [bnd, (v, [], ty3_of_field2, VarE (locs_var))]
                                                let curw' = SoAWin dcon_next _field_cur
                                                bod <- go isFirstPacked m1g m2g curw' fenv rst_vlocs rst_tys indirections_env denv tenv''
                                                return $ mkLets dcon_nxt bod
                                -- VS: TODO: needs to be fixed when packed type is not self recursive.
                                False -> do
                                   let ty3_of_field = getCursorizeTyFromLocVar' Nothing useMutableCursorsCall ploc
                                   let ty3_of_field2 :: Ty3 = getCursorizeTyFromLocVar Nothing useMutableCursorsCall ploc
                                   let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                                   let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur                              
                                   let tenv' =
                                              M.union
                                                ( M.fromList
                                                    [ (locs_var, ty3_of_field),
                                                      (v, ty3_of_field)
                                                    ]
                                                )
                                                tenvgoarg
                                       loc_bind = case M.lookup v indirections_env of
                                              -- This is the first packed value. We can unpack this.
                                              Nothing ->
                                                (locs_var, [], ty3_of_field2, VarE cur)
                                              -- We need to access this using a random access node
                                              Just (_var_loc, ind_var) ->
                                                (locs_var, [], ty3_of_field2, VarE ind_var)
                                   bod <- go isFirstPacked m1g m2g curw fenv rst_vlocs rst_tys indirections_env denv tenv'
                                   return $ mkLets [loc_bind, (v, [], ty3_of_field2, VarE locs_var)] bod

                        -- Flip canBind to indicate that the subsequent fields
                        --           -- should be added to the dependency environment.
                        --           bod <- go curw fenv rst_vlocs rst_tys False denv tenv'' -- (toEndV v)
                        --           return $
                        --             mkLets
                        --               [ ((loc_var), [], ty3_of_field2, VarE cur),
                        --                 (v, [], ty3_of_field2, VarE (loc_var))
                        --               ]
                        --               bod
                                  


                        -- PackedTy tycon ploc -> do
                        --   -- Two cases
                        --   -- If the PackedTy is the same tycon then
                        --   -- If the PackedTy is not the same tycon
                        --   let datacons = getConOrdering ddfs tycon
                        --   let isSameTycon = if (elem dcon datacons) then True else False
                        --   case isSameTycon of
                        --     True -> do
                        --       let ty3_of_field = case ploc of
                        --             Single _ -> CursorTy
                        --             SoA _ fl -> CursorArrayTy (1 + length fl)
                        --       let ty3_of_field2 :: Ty3 = case ploc of
                        --             Single _ -> CursorTy
                        --             SoA _ fl -> CursorArrayTy (1 + length fl)

                        --       let tenv' = M.insert v (MkTy2 ty3_of_field) tenv
                        --       let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                        --       -- let cur = fromJust $ L.lookup (dcon, field_idx) field_cur
                        --       let cur = dcur
                        --       loc_var <- lookupVariable loc fenv
                        --       if canBind
                        --         then do
                        --           let tenv'' = M.insert (loc_var) (MkTy2 ty3_of_field) tenv'
                        --           -- Flip canBind to indicate that the subsequent fields
                        --           -- should be added to the dependency environment.
                        --           dcon_next <- gensym $ toVar $ (fromVar dcur) ++ "_next"
                        --           let end_fields = map (\(key, varr) -> varr) _field_cur
                        --           let makeCurArr = Ext $ MakeCursorArray (1 + length (end_fields)) ([dcon_next] ++ end_fields)
                        --           let let_mk_cur_arr = (loc_var, [], CursorArrayTy (1 + length (end_fields)), makeCurArr)
                        --           let dcon_nxt = [(dcon_next, [], CursorTy, Ext $ AddCursor dcur (LitE 1))] ++ [let_mk_cur_arr, (v, [], CursorArrayTy (1 + length (end_fields)), VarE (loc_var))]
                        --           -- make the new curw type
                        --           -- this consists of incrementing the data constructor buffer by one and all the rest of the fields
                        --           let curw' = SoAWin dcon_next _field_cur
                        --           bod <- go curw' fenv rst_vlocs rst_tys False denv tenv'' -- (toEndV v)
                        --           return $ mkLets dcon_nxt bod
                        --         else do
                        --           -- Cannot read this. Instead, we add it to DepEnv.
                        --           let denv' = M.insertWith (++) (loc) [(v, [], ty3_of_field2, VarE (loc_var))] denv
                        --           go curw fenv rst_vlocs rst_tys False denv' tenv' -- (toEndV v)




                        --     False -> do
                        --       let ty3_of_field = case ploc of
                        --             Single _ -> CursorTy
                        --             SoA _ fl -> CursorArrayTy (1 + length fl)
                        --       let ty3_of_field2 :: Ty3 = case ploc of
                        --             Single _ -> CursorTy
                        --             SoA _ fl -> CursorArrayTy (1 + length fl)
                        --       let tenv' = M.insert v (MkTy2 ty3_of_field) tenv
                        --       let field_idx = fromJust $ L.elemIndex (v, locarg) vlocs1
                        --       let cur = fromJust $ L.lookup (dcon, field_idx) _field_cur
                        --       -- let cur = dcur
                        --       loc_var <- lookupVariable loc fenv
                        --       if canBind
                        --         then do
                        --           let tenv'' = M.insert (loc_var) (MkTy2 ty3_of_field) tenv'
                        --           -- Flip canBind to indicate that the subsequent fields
                        --           -- should be added to the dependency environment.
                        --           bod <- go curw fenv rst_vlocs rst_tys False denv tenv'' -- (toEndV v)
                        --           return $
                        --             mkLets
                        --               [ ((loc_var), [], ty3_of_field2, VarE cur),
                        --                 (v, [], ty3_of_field2, VarE (loc_var))
                        --               ]
                        --               bod
                        --         else do
                        --           -- Cannot read this. Instead, we add it to DepEnv.
                        --           let denv' = dbgTrace (minChatLvl) "Printing in packedTy unpack dcon: " dbgTrace (minChatLvl) (sdoc (loc)) dbgTrace (minChatLvl) "End in unpacking dcon.\n" M.insertWith (++) (loc) [((loc_var), [], ty3_of_field2, VarE cur), (v, [], ty3_of_field2, VarE (loc_var))] denv
                        --           bod <- go curw fenv rst_vlocs rst_tys False denv' tenv' -- (toEndV v)
                        --           -- VS: [05.11.2025] This is a hack to ensure that the location variable is not undefined.
                        --           -- If we have serialized packed types that are not self recursive, we still have to release
                        --           -- The let binding and just adding it to the depenv is not enough.
                        --           -- There should be a careful look at why this is and if this is functionally correct.
                        --           return $
                        --             mkLets
                        --               [((loc_var), [], ty3_of_field2, VarE cur), (v, [], ty3_of_field2, VarE (loc_var))]
                        --               bod  


                          
                        _ -> error $ "unpackWitnAbsRAN: TODO: Unexpected field " ++ sdoc (v, loc) ++ ":" ++ sdoc ty
                _ -> error $ "unpackWitnAbsRAN: Unexpected numnber of varible, type pairs: " ++ show (vlocs, tys)

    -- We have access to all fields in this constructor, and can create
    -- bindings for everything. We begin by unpacking the random access nodes.
    unpackWithRelRAN :: Var -> PassM Exp3
    unpackWithRelRAN field_cur =
      -- ran_mp is a map from a variable to a tuple containing it's location and
      -- the RAN field it depends on. Consider this constructor:
      --
      --     (Node* [(ran_y3, loc_ran_y3), (n1, loc_n1) , (x2 , loc_x2), (y3 , loc_y3)] ...),
      --
      -- it will be the map:
      --
      --     (y3 -> (loc_y3, ran_y3))
      let ran_mp =
            case numRANsDataCon (M.map (fmap unTy2) ddfs) (fromRANDataCon dcon) of
              0 -> M.empty
              n ->
                let -- Random access nodes occur immediately after the tag
                    inds = L.take n $ L.drop 1 vlocs1
                    -- Everything else is a regular consturctor field,
                    -- which depends on some random access node
                    data_fields = reverse $ L.take n (reverse vlocs1)
                    (vars, var_locargs) = unzip data_fields
                    var_locs =
                      map
                        ( \lc_arg -> case (M.lookup (fromLocVarToFreeVarsTy (toLocVar lc_arg)) freeVarToVarEnv) of
                            Just v' -> v'
                            Nothing -> error "cursorizeLet: unexpected location variable"
                        )
                        var_locargs
                 in M.fromList $ zip vars (zip var_locs (map (\(x, y) -> (x, (unwrapLocVar . toLocVar) y)) inds))
       in go field_cur vlocs1 tys1 ran_mp denv1 (M.insert field_cur (MkTy2 CursorTy) tenv1)
      where
        go :: Var -> [(Var, LocArg)] -> [Ty2] -> M.Map Var (Var, (Var, Var)) -> DepEnv -> TyEnv Var Ty2 -> PassM Exp3
        go cur vlocs tys indirections_env denv tenv = do
          case (vlocs, tys) of
            ([], []) -> do 
                         (rhs, _, _) <- processRhs m1 m2 freeVarToVarEnv denv tenv
                         return rhs
            ((v, locarg) : rst_vlocs, (MkTy2 ty) : rst_tys) ->
              let loc = toLocVar locarg
                  locsTy3 = getCursorizeTyFromLocVar Nothing useMutableCursorsCall loc
                  locsTy2 = getCursorizeTyFromLocVar' Nothing useMutableCursorsCall loc
                  locs_var = case (M.lookup (fromLocVarToFreeVarsTy loc) freeVarToVarEnv) of
                    Just v' -> v'
                    Nothing -> error "cursorizeLet: unexpected location variable"
               in case ty of
                    -- Int, Sym, or Bool
                    _ | isScalarTy ty -> do
                      (tenv', binds, m1', m2') <- scalarBinds True freeVarToVarEnv m1 m2 ty v locs_var locarg tenv
                      let loc_bind = case M.lookup v indirections_env of
                            -- This appears before the first packed field. Unpack it
                            -- in the usual way.
                            Nothing ->
                              (locs_var, [], locsTy3, VarE cur)
                            -- We need to read this using a random access node
                            Just (_var_loc, (ind_var, ind_loc)) ->
                              (locs_var, [], locsTy3, Ext $ AddCursor ind_loc (VarE ind_var))
                          binds' = loc_bind : binds
                          tenv'' = M.insert locs_var locsTy2 tenv'
                      bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv''
                      return $ mkLets binds' bod
                    PackedTy {} -> do
                      tmp_loc <- gensym "loc"
                      let tenv' =
                            M.union
                              ( M.fromList
                                  [ (locs_var, locsTy2),
                                    (v, locsTy2)
                                  ]
                              )
                              tenv
                          loc_binds = case M.lookup v indirections_env of
                            -- This is the first packed value. We can unpack this.
                            Nothing ->
                              [(locs_var, [], locsTy3, VarE cur)]
                            -- We need to access this using a random access node
                            Just (_var_loc, (ind_var, ind_loc)) ->
                              [ (tmp_loc, [], locsTy3, Ext $ AddCursor ind_loc (VarE ind_var)),
                                (locs_var, [], locsTy3, Ext $ AddCursor tmp_loc (LitE 8))
                              ]
                      bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv'
                      return $ mkLets (loc_binds ++ [(v, [], locsTy3, VarE locs_var)]) bod
                    _ -> error $ "unpackWithRelRAN: Unexpected field " ++ sdoc (v, loc) ++ ":" ++ sdoc ty
            _ -> error $ "unpackWithRelRAN: Unexpected numnber of varible, type pairs: " ++ show (vlocs, tys)

    -- Generate bindings for unpacking int fields. A convenient
    scalarBinds :: Bool -> M.Map FreeVarsTy Var -> MutableLocPtsToEnv -> MutableLocOldValueEnv -> OldTy2 -> Var -> Var -> LocArg -> TyEnv Var Ty2 -> PassM (TyEnv Var Ty2, [(Var, [()], Ty3, Exp3)], MutableLocPtsToEnv, MutableLocOldValueEnv)
    scalarBinds varAlive fenv m1 m2 ty v loc lcarg tenv = do
      tmp <- gensym "read_scalar_tuple"
      let locsTy2 = getCursorizeTyFromLocVar (getModality lcarg) useMutableCursorsCall (toLocVar lcarg)
          locsTy3 = getCursorizeTyFromLocVar' (getModality lcarg) useMutableCursorsCall (toLocVar lcarg)
          locsUrTy = getCursorizeTyFromLocVar'' (getModality lcarg) useMutableCursorsCall (toLocVar lcarg)
      -- Note that the location is not added to the type environment here.
      -- The caller of this fn will do that later, depending on whether we're
      -- binding the location now or later via DepEnv.
      let s = mkScalar ty
          tenv' =
            M.union
              ( M.fromList
                  [ (tmp, MkTy2 (ProdTy [ty, locsUrTy])),
                    (v, MkTy2 ty),
                    (toEndV v, locsTy3)
                  ]
              )
              tenv

          ty' = stripTyLocs ty

          binds =
            [ (tmp, [], ProdTy [ty', locsTy2], Ext $ ReadScalar s loc),
              (v, [], ty', ProjE 0 (VarE tmp)),
              (toEndV v, [], locsTy2, ProjE 1 (VarE tmp))
            ]
      let mut_loc = findMutableLocationPointingToVar loc m1
      (m1', binds') <- case mut_loc of 
                            Nothing -> dbgTrace (minChatLvl) "Print inside scalar binds: " dbgTrace (minChatLvl) (sdoc (mut_loc, loc)) dbgTrace (minChatLvl) "End printing inside scalar binds!\n" return (m1, []) 
                            Just l -> do
                              if varAlive 
                              then do
                                let m1inner = updateMutableLocPtsToEnv l m1 (toEndV v, Just l, Nothing, S.empty) False
                                void_var <- gensym "void"
                                dflags <- getDynFlags
                                let size_of_scalar = sizeOfTyD dflags ty
                                let lvar = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy l)
                                let bump_bns = [(void_var, [], ProdTy [], Ext $ BumpCursorMutable lvar (LitE (fromJust $ size_of_scalar)))]
                                dbgTrace (minChatLvl) "Print inside scalar binds: " dbgTrace (minChatLvl) (sdoc (mut_loc, loc, bump_bns)) dbgTrace (minChatLvl) "End printing inside Just l case scalar binds!\n"  return (m1inner, bump_bns)
                              else do
                                    -- we are still updating the env, even though the field is dead.
                                    -- This makes the algorithm work fine.
                                    -- otherwise later on, we may get unnecessary bump mutable locations.
                                    let m1inner = updateMutableLocPtsToEnv l m1 (toEndV v, Just l, Nothing, S.empty) False
                                    return (m1inner, []) 
      return (tenv', binds ++ binds', m1', m2)

giveStarts :: TyEnv Var Ty2 -> M.Map FreeVarsTy Var -> Bool -> Bool -> Bool -> Bool -> MutableLocPtsToEnv -> MutableLocOldValueEnv -> OldTy2 -> Exp3 -> PassM Exp3
giveStarts tenv fenv useMutableCursorsCall isInsideTimeIt frec nonSelfCall mlocptsenv moldenv ty e = do
  let findOldValueVarByAlias var =
        L.foldr
          (\(_k, (oldv, _lc, _reg, aliases)) acc ->
              if var == oldv || S.member var aliases
              then Just oldv
              else acc)
          Nothing
          (M.toList moldenv)
  case ty of
    PackedTy _ loc -> do
                      if useMutableCursorsCall
                      then case M.lookup loc moldenv of 
                                        Nothing -> case e of
                                                       VarE vv -> case findOldValueVarByAlias vv of
                                                                    Just oldv -> case loc of
                                                                                  Single{} -> if nonSelfCall
                                                                                              then do
                                                                                                   copy_var <- gensym "copy_start"
                                                                                                   take_address <- gensym "copy_address"
                                                                                                   let copy_bnds = [ (copy_var, [], CursorTy, VarE oldv)
                                                                                                                   , (take_address, [], MutCursorTy, Ext $ AddrOfCursor (VarE copy_var))
                                                                                                                   ]
                                                                                                   return $ mkLets copy_bnds (VarE take_address)
                                                                                              else do
                                                                                                   take_address <- gensym "address"
                                                                                                   let additional_bnd = (take_address, [], MutCursorTy, Ext $ AddrOfCursor (VarE oldv))
                                                                                                   return $ mkLets [additional_bnd] (VarE take_address)
                                                                                  SoA{} -> if nonSelfCall
                                                                                           then do
                                                                                                copy_var <- gensym "copy_start"
                                                                                                void_var <- gensym "void"
                                                                                                let copy_ty = getCursorizeTyFromLocVar Nothing useMutableCursorsCall loc
                                                                                                let copy_bnds = [ (copy_var, [], copy_ty, Ext $ InitCursor copy_ty)
                                                                                                                , (void_var, [], ProdTy [], Ext $ MemCpy copy_var oldv copy_ty)
                                                                                                                ]
                                                                                                return $ mkLets copy_bnds (VarE copy_var)
                                                                                           else return $ VarE oldv
                                                                    Nothing -> return $ VarE vv
                                                       _ -> case e of 
                                                              MkProdE ls -> do 
                                                                            case ls of 
                                                                                   (VarE return_var):rst -> do 
                                                                                                       case M.lookup return_var tenv of 
                                                                                                             Nothing -> return $ mkProj 0 e
                                                                                                             Just ty -> case (unTy2 ty) of 
                                                                                                                           MutCursorTy -> return $ mkProj 0 e
                                                                                                                           CursorTy -> do
                                                                                                                                       take_address <- gensym "address"
                                                                                                                                       let additional_bnd = (take_address, [], MutCursorTy, Ext $ AddrOfCursor (mkProj 0 e)) 
                                                                                                                                       return $ mkLets [additional_bnd] (VarE take_address)
                                                                                                                           -- Vidush: Kind of bad, since this does not ascertain the kind of the cursor
                                                                                                                           PackedTy _ l -> do
                                                                                                                                           case l of 
                                                                                                                                               Single{} -> do 
                                                                                                                                                           take_address <- gensym "address"
                                                                                                                                                           let additional_bnd = (take_address, [], MutCursorTy, Ext $ AddrOfCursor (mkProj 0 e)) 
                                                                                                                                                           return $ mkLets [additional_bnd] (VarE take_address)
                                                                                                                                               SoA{} -> case isInsideTimeIt of 
                                                                                                                                                               False -> return $ mkProj 0 e
                                                                                                                                                               True -> do
                                                                                                                                                                       copy_var <- gensym "copy_start_timeit"
                                                                                                                                                                       let variable_holding_start_vals = return_var
                                                                                                                                                                           ty_of_loc = getCursorizeTyFromLocVar Nothing useMutableCursorsCall loc
                                                                                                                                                                           make_copy_binds = [ (copy_var, [], ty_of_loc, Ext $ InitCursor ty_of_loc), ("_", [], ProdTy [], Ext $ MemCpy copy_var return_var ty_of_loc)]
                                                                                                                                                                       return $ mkLets make_copy_binds $ VarE copy_var
                                                                                                                           _ -> return $ mkProj 0 e
                                                                                   _ -> return $ mkProj 0 e                                                                     
                                                              _ -> dbgTrace (minChatLvl) "Print in give starts: " dbgTrace (minChatLvl) (sdoc (loc, e)) dbgTrace (minChatLvl) "End in give starts Packed Nothing!\n" return $ mkProj 0 e --error $ "Expected to have loc in env!!" ++ show (loc, moldenv)
                                        Just (oldv, _oldl, _, _) ->
                                          let locName = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy loc)
                                              locTy = M.lookup locName tenv
                                          in case frec of
                                               True ->
                                                 case loc of
                                                   Single{} ->
                                                     if nonSelfCall
                                                     then do
                                                       copy_var <- gensym "copy_start"
                                                       take_address <- gensym "copy_address"
                                                       let copy_bnds =
                                                             [ (copy_var, [], CursorTy, VarE oldv)
                                                             , (take_address, [], MutCursorTy, Ext $ AddrOfCursor (VarE copy_var))
                                                             ]
                                                       dbgTrace (minChatLvl) "Print in give starts: " dbgTrace (minChatLvl) (sdoc (loc, oldv, locName, locTy)) dbgTrace (minChatLvl) "End in give starts non-tail Single copy!\n" return $ mkLets copy_bnds (VarE take_address)
                                                     else do
                                                       take_address <- gensym "address"
                                                       let additional_bnd = (take_address, [], MutCursorTy, Ext $ AddrOfCursor (VarE oldv))
                                                       dbgTrace (minChatLvl) "Print in give starts: " dbgTrace (minChatLvl) (sdoc (loc, oldv, locName, locTy)) dbgTrace (minChatLvl) "End in give starts tail rec Single!\n" return $ mkLets [additional_bnd] (VarE take_address)
                                                   SoA{} -> do
                                                     copy_var <- gensym "copy_address"
                                                     let ty_of_loc = getCursorizeTyFromLocVar Nothing useMutableCursorsCall loc
                                                         make_copy_binds =
                                                           [ (copy_var, [], ty_of_loc, Ext $ InitCursor ty_of_loc)
                                                           , ("_", [], ProdTy [], Ext $ MemCpy copy_var oldv ty_of_loc)
                                                           ]
                                                     dbgTrace (minChatLvl) "Print in give starts: " dbgTrace (minChatLvl) (sdoc (loc, oldv, locName, locTy)) dbgTrace (minChatLvl) "End in give starts tail rec but SoA!\n" return $ mkLets make_copy_binds $ VarE copy_var
                                               _ ->
                                                 dbgTrace (minChatLvl) "Print in give starts: " dbgTrace (minChatLvl) (sdoc (loc, oldv, locName, locTy)) dbgTrace (minChatLvl) "End in give starts!\n" return $ VarE oldv
                      else return $ mkProj 0 e
    -- NOTE : mkProj . MkProdE == id
    ProdTy tys -> do
                  args <- mapM (\(ty', n) -> giveStarts tenv fenv useMutableCursorsCall isInsideTimeIt frec nonSelfCall mlocptsenv moldenv ty' (mkProj n e)) (zip tys [0 ..])
                  return $ MkProdE args 
    CursorArrayTy sz -> case e of 
                          VarE v -> let mutloc = findMutableLocationPointingToVar v mlocptsenv
                                     in case mutloc of 
                                              Nothing -> case findOldValueVarByAlias v of
                                                              Nothing -> dbgTrace (minChatLvl) "Print in give starts: " dbgTrace (minChatLvl) (sdoc (v, mlocptsenv)) dbgTrace (minChatLvl) "End in give starts Nothing!\n" return e
                                                              Just oldv -> dbgTrace (minChatLvl) "Print in give starts old value: " dbgTrace (minChatLvl) (sdoc (v, oldv)) dbgTrace (minChatLvl) "End in give starts old value!\n" return $ VarE oldv
                                              Just ml -> do 
                                                         let mlVarName = dbgTrace (minChatLvl) "Print in give starts: " dbgTrace (minChatLvl) (sdoc (v, ml, mlocptsenv)) dbgTrace (minChatLvl) "End in give starts Just ml!\n" getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy ml)
                                                         if nonSelfCall && useMutableCursorsCall
                                                         then do
                                                              copy_var <- gensym "copy_start"
                                                              void_var <- gensym "void"
                                                              let copy_ty = CursorArrayTy sz
                                                              let copy_binds = [(copy_var, [], copy_ty, Ext $ InitCursor copy_ty),
                                                                                (void_var, [], ProdTy [], Ext $ MemCpy copy_var mlVarName copy_ty)]
                                                              return $ mkLets copy_binds (VarE copy_var)
                                                         else return $ VarE mlVarName
                          _ -> return e  
    _ -> case e of 
             VarE vv -> let mutl = dbgTrace (minChatLvl) "Print in give starts VarE v case: " dbgTrace (minChatLvl) (sdoc (e)) dbgTrace (minChatLvl) "End in give starts VarE v.\n" findMutableLocationPointingToVar vv mlocptsenv
                         in case mutl of 
                                Nothing -> case findOldValueVarByAlias vv of
                                             Nothing -> dbgTrace (minChatLvl) "Print in give starts rest of the case: " dbgTrace (minChatLvl) (sdoc (e, mlocptsenv)) dbgTrace (minChatLvl) "End in give starts rest of the case 1!\n" return e
                                             Just oldv -> dbgTrace (minChatLvl) "Print in give starts old value: " dbgTrace (minChatLvl) (sdoc (vv, oldv)) dbgTrace (minChatLvl) "End in give starts old value case 2!\n" return $ VarE oldv
                                Just ml -> let mlName = getVarNameFromFreeVar fenv (fromLocVarToFreeVarsTy ml)
                                             in do
                                                  dbgTrace (minChatLvl) "Print in give starts rest of the case: " dbgTrace (minChatLvl) (sdoc (e, mlocptsenv, mlName)) dbgTrace (minChatLvl) "End in give starts rest of the case 2!\n" (return ())
                                                  case M.lookup mlName tenv of
                                                    Just (MkTy2 MutCursorTy) ->
                                                      if nonSelfCall && useMutableCursorsCall
                                                      then do
                                                        deref_copy <- gensym "deref_copy"
                                                        copy_address <- gensym "copy_address"
                                                        let copy_bnds =
                                                              [ (deref_copy, [], CursorTy, Ext $ DerefMutCursor mlName)
                                                              , (copy_address, [], MutCursorTy, Ext $ AddrOfCursor (VarE deref_copy))
                                                              ]
                                                        return $ mkLets copy_bnds (VarE copy_address)
                                                      else return $ VarE mlName
                                                    _ -> return $ VarE mlName

             _ -> dbgTrace (minChatLvl) "Print in give starts _ case: " dbgTrace (minChatLvl) (sdoc (e)) dbgTrace (minChatLvl) "End in give starts wildcard v.\n" return e


projValTy :: (Out a) => UrTy a -> UrTy a
projValTy = projTy 0

projEndsTy :: (Out a) => UrTy a -> UrTy a
projEndsTy = projTy 1

-- -- | Bindings for a letregion
-- regionToBinds :: M.Map FreeVarsTy Var -> Bool -> Region -> RegionSize -> PassM [(Var, [()], Ty3, Exp3)]
-- regionToBinds freeVarToVarEnv for_parallel_allocs r sz = do
--   case r of
--     VarR{} -> error $ "Unexpected VarR in Cursorize." ++ sdoc r
--     GlobR v mul -> do
--                    let mul' = go mul
--                    let endv = toEndV v
--                    if for_parallel_allocs
--                    then return $ [ (v       , [], CursorTy, Ext (NewParBuffer mul')) , ((endv), [], CursorTy, Ext (EndOfBuffer mul'))]
--                    else return $ [ (v       , [], CursorTy, Ext (NewBuffer mul'))
--                                  , (endv, [], CursorTy, Ext (EndOfBuffer mul'))]
--     DynR v mul  -> do
--                    let mul' = go mul
--                    if for_parallel_allocs
--                    then return $ [ (v       , [], CursorTy, Ext$ ScopedParBuffer mul')
--                                  , (toEndV v, [], CursorTy, Ext$ EndOfBuffer mul')]
--                    else return $ [ (v       , [], CursorTy, Ext$ ScopedBuffer mul')
--                                  , (toEndV v, [], CursorTy, Ext$ EndOfBuffer mul')]
--     -- TODO: docs
--     MMapR _v    -> return $ []

--     -- TODO: SoA Region
--     SoAR dcreg fieldRegs -> do
--                             dcreg_binds <- regionToBinds freeVarToVarEnv for_parallel_allocs dcreg sz
--                             field_binds <- concatMapM (\(key, field_reg) -> regionToBinds freeVarToVarEnv for_parallel_allocs field_reg sz) fieldRegs
--                             -- Make the cursor array
--                             let reg_to_reg_var = regionToVar r
--                             regions_var <- case (M.lookup (fromRegVarToFreeVarsTy reg_to_reg_var) freeVarToVarEnv) of
--                                                 Just v -> return $ v
--                                                 Nothing -> gensym "reg_ptr"
--                             field_reg_vars <- mapM (\(key, field_reg) -> case (M.lookup (fromRegVarToFreeVarsTy (regionToVar field_reg)) freeVarToVarEnv) of
--                                                                                       Just v -> v
--                                                                                       Nothing -> case field_reg of
--                                                                                                     VarR v -> return $ v
--                                                                                                     GlobR v _ -> return $ v
--                                                                                                     DynR v _ -> return $ v
--                                                                                                     MMapR v -> return $ v
--                                                                                                     SoAR _ _ -> gensym "reg_ptr"
--                                                    ) fieldRegs
--                               dc_reg_var <- case (M.lookup (fromRegVarToFreeVarsTy (regionToVar dcreg)) freeVarToVarEnv) of
--                                                 Just v -> return $ v
--                                                 Nothing -> case dcreg of
--                                                                  VarR v -> return $ v
--                                                                  GlobR v _ -> return $ v
--                                                                  DynR v _ -> return $ v
--                                                                  MMapR v -> return $ v
--                                                                  SoAR _ _ -> error "data constructor region cannot be SoA."
--                               let make_cur_array_bind = (regions_var, [], CursorArrayTy (1 + length (field_reg_vars)), Ext $ MakeCursorArray (1 + length (field_reg_vars)) ([dc_reg_var] ++ field_reg_vars))
--                              in return $ dcreg_binds ++ field_binds ++ [make_cur_array_bind]

--  where
--   go mul =
--     case sz of
--       BoundedSize 0 -> mul
--       BoundedSize x -> Bounded x
--       Undefined     -> mul

-- regionToBinds :: M.Map FreeVarsTy Var -> Bool -> Region -> RegionSize -> PassM ([(Var, [()], Ty3, Exp3)], M.Map FreeVarsTy Var)
-- regionToBinds freeVarToVarEnv for_parallel_allocs r sz = do
--   case r of
--     VarR{} -> error $ "Unexpected VarR in Cursorize." ++ sdoc r
--     GlobR v mul -> do
--                    let mul' = go mul
--                    let endv = toEndV v
--                    let bnds = if for_parallel_allocs
--                               then [ (v       , [], CursorTy, Ext (NewParBuffer mul')) , (endv, [], CursorTy, Ext (EndOfBuffer mul'))]
--                               else [ (v       , [], CursorTy, Ext (NewBuffer mul'))
--                                  , (endv, [], CursorTy, Ext (EndOfBuffer mul'))]
--                    return (bnds, freeVarToVarEnv)
--     DynR v mul  -> do
--                    let mul' = go mul
--                    let bnds = if for_parallel_allocs
--                               then [ (v       , [], CursorTy, Ext (ScopedParBuffer mul'))
--                                  , (toEndV v, [], CursorTy, Ext (EndOfBuffer mul'))]
--                               else [ (v       , [], CursorTy, Ext (ScopedBuffer mul'))
--                                  , (toEndV v, [], CursorTy, Ext (EndOfBuffer mul'))]
--                    return (bnds, freeVarToVarEnv)
--     -- TODO: docs
--     MMapR _v    -> return ([], freeVarToVarEnv)

--     -- TODO: SoA Region
--     SoAR dcreg fieldRegs -> do
--                             (dcreg_binds, freeVarToVarEnv') <- regionToBinds freeVarToVarEnv for_parallel_allocs dcreg sz
--                             field_binds_pairs <- fmap concat $ mapM (\(key, field_reg) -> regionToBinds freeVarToVarEnv for_parallel_allocs field_reg sz) fieldRegs
--                             let field_binds = map fst field_binds_pairs
--                             let field_new_maps = map snd field_binds_pairs
--                             -- Make the cursor array
--                             let reg_to_reg_var = regionToVar r
--                             regions_var <- case M.lookup (fromRegVarToFreeVarsTy reg_to_reg_var) freeVarToVarEnv of
--                                                 Just v -> return v
--                                                 Nothing -> gensym "reg_ptr"
--                             let freeVarToVarEnv'' = M.insert (fromRegVarToFreeVarsTy reg_to_reg_var) regions_var freeVarToVarEnv'
--                             field_reg_keys_vars <- mapM (\(key, field_reg) -> do
--                                                                               case M.lookup (fromRegVarToFreeVarsTy (regionToVar field_reg)) freeVarToVarEnv of
--                                                                                       Just v -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
--                                                                                       Nothing -> case field_reg of
--                                                                                                     VarR v -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
--                                                                                                     GlobR v _ -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
--                                                                                                     DynR v _ -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
--                                                                                                     MMapR v -> return (fromRegVarToFreeVarsTy (regionToVar field_reg), v)
--                                                                                                      SoAR _ _ -> do
--                                                                                                                  new_name <- gensym "reg_ptr"
--                                                                                                                  return (fromRegVarToFreeVarsTy (regionToVar field_reg), new_name)
--                                                    ) fieldRegs
--                             let field_reg_keys = map fst field_reg_keys_vars
--                             let field_reg_vars = map snd field_reg_keys_vars
--                             let freeVarToVarEnv''' = foldr (\(key, var) acc -> M.insert key var acc) freeVarToVarEnv'' field_reg_keys_vars
--                             dc_reg_var <- case M.lookup (fromRegVarToFreeVarsTy (regionToVar dcreg)) freeVarToVarEnv of
--                                                 Just v -> return v
--                                                 Nothing -> case dcreg of
--                                                                  VarR v -> return v
--                                                                  GlobR v _ -> return v
--                                                                  DynR v _ -> return v
--                                                                  MMapR v -> return v
--                                                                  SoAR _ _ -> error "data constructor region cannot be SoA."
--                             let freeVarToVarEnv'''' = M.insert (fromRegVarToFreeVarsTy (regionToVar dcreg)) dc_reg_var freeVarToVarEnv'''
--                             let make_cur_array_bind = (regions_var, [], CursorArrayTy (1 + length field_reg_vars), Ext $ MakeCursorArray (1 + length field_reg_vars) ([dc_reg_var] ++ field_reg_vars))
--                             return (dcreg_binds ++ field_binds ++ [make_cur_array_bind], freeVarToVarEnv'''')

--  where
--   go mul =
--     case sz of
--       BoundedSize 0 -> mul
--       BoundedSize x -> Bounded x
--       Undefined     -> mul

regionToBinds :: M.Map FreeVarsTy Var -> Bool -> Region -> RegionSize -> EndRegionModality -> PassM ([(Var, [()], Ty3, Exp3)], M.Map FreeVarsTy Var)
regionToBinds freeVarToVarEnv for_parallel_allocs r sz endregmod = do
  case r of
    VarR {} -> error $ "Unexpected VarR in Cursorize." ++ sdoc r
    GlobR v mul -> do
      let mul' = go mul
      let endv = toEndV v
      let endregcursorty = case endregmod of 
                                L2.RegionImmutable -> CursorTy 
                                L2.RegionMutable -> MutCursorTy
      -- (deref_bnds, end_cursor_val) <- if (endregmod == L2.RegionMutable)
      --               then do 
      --                 end_cursor_val <- gensym "end_cursor_val"
      --                 return ([(end_cursor_val, [], CursorTy, Ext (EndOfBuffer mul'))], Just end_cursor_val)
      --               else return ([], Nothing)
      let bnds =
            if for_parallel_allocs
              then [(v, [], CursorTy, Ext (NewParBuffer mul')), (endv, [], CursorTy, Ext (EndOfBuffer mul' endregmod))]
              else
                [ (v, [], CursorTy, Ext (NewBuffer mul' endregmod)),
                  (endv, [], endregcursorty, Ext (EndOfBuffer mul' endregmod))
                ] 
                
      return (bnds, freeVarToVarEnv)
    DynR v mul -> do
      let mul' = go mul
      let bnds =
            if for_parallel_allocs
              then
                [ (v, [], CursorTy, Ext (ScopedParBuffer mul')),
                  (toEndV v, [], CursorTy, Ext (EndOfBuffer mul' endregmod))
                ]
              else
                [ (v, [], CursorTy, Ext (ScopedBuffer mul')),
                  (toEndV v, [], CursorTy, Ext (EndOfBuffer mul' endregmod))
                ]
      return (bnds, freeVarToVarEnv)
    -- TODO: docs
    MMapR _v -> return ([], freeVarToVarEnv)
    -- TODO: SoA Region
    SoAR dcreg fieldRegs -> do
      (dcreg_binds, _freeVarToVarEnv) <- regionToBinds freeVarToVarEnv for_parallel_allocs dcreg sz L2.RegionImmutable
      field_binds_pairs <- mapM (\(key, field_reg) -> case regionToVar field_reg of 
                                                             SingleR{} -> regionToBinds _freeVarToVarEnv for_parallel_allocs field_reg sz L2.RegionImmutable
                                                             -- We linearize these regions.
                                                             SoARv dc_reg fregs -> do 
                                                                                   case field_reg of
                                                                                          SoAR dcr frs -> do
                                                                                              let dc_bnds = case dcr of 
                                                                                                               GlobR v mul  -> let mul' = go mul
                                                                                                                                   endv = toEndV v
                                                                                                                                   bnds = [ (v, [], CursorTy, Ext (NewBuffer mul' L2.RegionImmutable)),
                                                                                                                                            (endv, [], CursorTy, Ext (EndOfBuffer mul' L2.RegionImmutable))
                                                                                                                                          ]
                                                                                                                                 in bnds
                                                                                                               _ -> error "not implemented"
                                                                                              fld_bnds <- concat <$> mapM (\((dcon, idx), fr) -> do 
                                                                                                                                      case fr of
                                                                                                                                         GlobR v mul  -> do 
                                                                                                                                                         let mul' = go mul
                                                                                                                                                         let endv = toEndV v
                                                                                                                                                         let ty :: Ty3 = CursorTy
                                                                                                                                                         let exp1 :: Exp3 = Ext (NewBuffer mul' L2.RegionImmutable)
                                                                                                                                                         let exp2 :: Exp3 = Ext (EndOfBuffer mul' L2.RegionImmutable)
                                                                                                                                                         let bnds = [ (v, [], ty, exp1),
                                                                                                                                                                      (endv, [], ty, exp2)
                                                                                                                                                                    ]
                                                                                                                                                         pure bnds
                                                                                                                                         _ -> error "Not implemented!"
                                                                                                                           
                                                                                                                 ) frs

                                                                                              pure (dc_bnds ++ fld_bnds, _freeVarToVarEnv)
                                                                                                                                
                                                                                       
                                                             
                                ) fieldRegs
      let field_binds = concatMap fst field_binds_pairs
      let field_new_maps = map snd field_binds_pairs
      let _freeVarToVarEnv' = foldr (\m acc -> M.union m acc) freeVarToVarEnv field_new_maps
      let freeVarToVarEnv' = M.union _freeVarToVarEnv' _freeVarToVarEnv
      -- Make the cursor array
      let reg_to_reg_var = regionToVar r
      regions_var <- case M.lookup (fromRegVarToFreeVarsTy reg_to_reg_var) freeVarToVarEnv' of
        Just v -> return v
        Nothing -> gensym "reg_ptr"
      let freeVarToVarEnv'' = M.insert (fromRegVarToFreeVarsTy reg_to_reg_var) regions_var freeVarToVarEnv'
      field_reg_keys_vars <-
        concat <$> mapM
          ( \(key, field_reg) -> do
              case M.lookup (fromRegVarToFreeVarsTy (regionToVar field_reg)) freeVarToVarEnv'' of
                Just v -> return [(fromRegVarToFreeVarsTy (regionToVar field_reg), v)]
                Nothing -> case field_reg of
                  VarR v -> return [(fromRegVarToFreeVarsTy (regionToVar field_reg), v)]
                  GlobR v _ -> return [(fromRegVarToFreeVarsTy (regionToVar field_reg), v)]
                  DynR v _ -> return [(fromRegVarToFreeVarsTy (regionToVar field_reg), v)]
                  MMapR v -> return [(fromRegVarToFreeVarsTy (regionToVar field_reg), v)]
                  SoAR dc fvar -> do
                                  let dcv = case dc of 
                                                  GlobR v _ -> (fromRegVarToFreeVarsTy (regionToVar dc), v) 
                                  let fvs = map (\(_, f) -> case f of 
                                                               GlobR v _ -> (fromRegVarToFreeVarsTy (regionToVar f), v)
                                                ) fvar
                                  return $ [dcv] ++ fvs
                                  
          )
          fieldRegs
      let field_reg_keys = map fst field_reg_keys_vars
      let field_reg_vars = map snd field_reg_keys_vars
      let field_end_reg_keys = map (\(R r) -> toEndVRegVar r) field_reg_keys
      freeVarToVarEnv''' <- foldrM (\key acc -> insertRegInVarEnv key acc) freeVarToVarEnv'' field_end_reg_keys
      let field_end_reg_vars =
            map
              ( \key -> case (M.lookup (fromRegVarToFreeVarsTy key) freeVarToVarEnv''') of
                  Just v -> v
                  Nothing -> error "cursorizeExp: regionToBinds: SoAR: unexpected end of region variable"
              )
              field_end_reg_keys
      let freeVarToVarEnv'''' = foldr (\(key, var) acc -> M.insert key var acc) freeVarToVarEnv''' field_reg_keys_vars
      dc_reg_var <- case M.lookup (fromRegVarToFreeVarsTy (regionToVar dcreg)) freeVarToVarEnv'''' of
        Just v -> return v
        Nothing -> case dcreg of
          VarR v -> return v
          GlobR v _ -> return v
          DynR v _ -> return v
          MMapR v -> return v
          SoAR _ _ -> error "data constructor region cannot be SoA."
      let freeVarToVarEnv''''' = M.insert (fromRegVarToFreeVarsTy (regionToVar dcreg)) dc_reg_var freeVarToVarEnv''''
      let dc_reg_end_var = toEndVRegVar (regionToVar dcreg)
      freeVarToVarEnv'''''' <- insertRegInVarEnv dc_reg_end_var freeVarToVarEnv'''''
      let dc_reg_end_var_name = case (M.lookup (fromRegVarToFreeVarsTy dc_reg_end_var) freeVarToVarEnv'''''') of
            Just v -> v
            Nothing -> error "cursorizeExp: regionToBinds: SoAR: unexpected end of region variable"
      let end_soa_reg = toEndVRegVar (regionToVar r)
      freeVarToVarEnv''''''' <- insertRegInVarEnv end_soa_reg freeVarToVarEnv''''''
      let end_soa_reg_name = case (M.lookup (fromRegVarToFreeVarsTy end_soa_reg) freeVarToVarEnv''''''') of
            Just v -> v
            Nothing -> error "cursorizeExp: regionToBinds: SoAR: unexpected end of region variable"
      let make_cur_array_bind = (regions_var, [], CursorArrayTy (1 + length field_reg_vars), mkMakeCursorArrayDbg regions_var ([dc_reg_var] ++ field_reg_vars))
      let make_end_cur_array_bind = (end_soa_reg_name, [], CursorArrayTy (1 + length field_end_reg_vars), mkMakeCursorArrayDbg end_soa_reg_name ([dc_reg_end_var_name] ++ field_end_reg_vars))
      return (dcreg_binds ++ field_binds ++ [make_cur_array_bind] ++ [make_end_cur_array_bind], freeVarToVarEnv''''''')
  where
    go mul =
      case sz of
        BoundedSize 0 -> mul
        BoundedSize x -> Bounded x
        Undefined -> mul

isBound :: Var -> TyEnv Var Ty2 -> Bool
isBound l m = M.member l m

-- ================================================================================
--                         Dilation Conventions
-- ================================================================================
-- Everything to do with dilation.  It should be possible to change
-- the dilated format by changing only this section.

-- | If an expression `e` returns type `T`, then a dilated version of
-- `e` returns a tuple (T,Cursors), where cursors contains a flat
-- record of end-cursors corresponding exactly to all the components
-- of T which are PackedTy.
newtype DiExp ex = Di ex
  deriving (Generic, Show, Read, Eq, Ord)

-- type DiExp = Exp

instance (Out ex) => Out (DiExp ex)

onDi :: (ex -> ex) -> DiExp ex -> DiExp ex
onDi f (Di x) = Di (f x)

fromDi :: DiExp ex -> ex
fromDi (Di x) = x

-- | Project the cursor package from a dilated expression, contains pointers
-- to all the ENDs.
projEnds :: HasCallStack => DiExp Exp3 -> Exp3
projEnds (Di e) = mkProj 1 e

-- | Project the original value from a dilated expression.
projVal :: DiExp Exp3 -> Exp3
projVal (Di e) = mkProj 0 e

-- | Constructor that combines a regular expression with a list of
-- corresponding end cursors.
mkDi :: Exp3 -> [Exp3] -> DiExp Exp3
mkDi x [] = Di $ MkProdE [x, MkProdE []]
mkDi x [o] = Di $ MkProdE [x, o]
mkDi x ls = Di $ MkProdE [x, MkProdE ls]

curDict :: UrTy a -> UrTy a
curDict (SymDictTy ar _ty) = SymDictTy ar CursorTy
curDict ty = ty
