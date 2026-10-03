{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
-- | Replace calls to copy functions with tagged indirection nodes
module Gibbon.Passes.RemoveCopies where

import qualified Data.Map as M

import Gibbon.Common
import Gibbon.DynFlags
import Gibbon.L2.Syntax

--------------------------------------------------------------------------------

-- Maps a location to a region
type LocEnv = M.Map LocVar RegVar

-- | Maps a location to @(root, byte offset from root)@ where that is
-- statically known.  Only constant offsets are tracked; a location built with
-- a data-dependent offset becomes its own root, so an unknown distance is
-- never mistaken for a known one.  See
-- Note [A value cannot be re-placed onto itself].
type OffEnv = M.Map LocVar (LocVar, Int)

learnOffset :: LocVar -> PreLocExp LocVar -> OffEnv -> OffEnv
learnOffset loc rhs oenv =
  learnTagOffset loc rhs $
  case rhs of
    AfterConstantLE k base ->
      let (root, off) = resolveOffset base oenv
       in M.insert loc (root, off + k) oenv
    AssignLE base -> M.insert loc (resolveOffset base oenv) oenv
    _ -> oenv
  where
    -- Offsets of a fully-factored location are tracked on its tag cursor
    -- ('getDconLoc'); @AfterConstantLE k@ on an SoA location offsets the tag
    -- buffer only.
    learnTagOffset l r env
      | not (isSoALoc l), GetDataConLocSoA src <- r =
          M.insert l (resolveOffset (getDconLoc src) env) env
      | isSoALoc l =
          case r of
            AfterConstantLE k base ->
              let (root, off) = resolveOffset (getDconLoc base) env
               in M.insert (getDconLoc l) (root, off + k) env
            AssignLE base -> M.insert (getDconLoc l) (resolveOffset (getDconLoc base) env) env
            GenSoALoc d _ | d /= getDconLoc l ->
              M.insert (getDconLoc l) (resolveOffset d env) env
            _ -> env
      | otherwise = env

resolveOffset :: LocVar -> OffEnv -> (LocVar, Int)
resolveOffset loc oenv = M.findWithDefault (loc, 0) loc oenv

-- | Bytes an indirection node occupies: one tag plus one tagged pointer.
-- 'Gibbon.Passes.Cursorize' lowers 'IndirectionE' to exactly this
-- (@end = from + 9@).
indirectionBytes :: Int
indirectionBytes = 9

-- | Bytes a factored indirection occupies in the TAG buffer: one tag plus one
-- cursor per buffer of the type.  It writes nothing into any other buffer.
-- See Note [A factored indirection lives in the tag buffer].
soaIndirectionTagBytes :: LocVar -> Int
soaIndirectionTagBytes loc = 1 + 8 * locBufferCount loc

-- | Does re-placing a value at @lout@ that currently lives at @lin@ write over
-- the value itself?  See Note [A value cannot be re-placed onto itself].
replacementOverlaps :: OffEnv -> LocVar -> LocVar -> Bool
replacementOverlaps oenv lin lout = overlapsBy indirectionBytes oenv lin lout

overlapsBy :: Int -> OffEnv -> LocVar -> LocVar -> Bool
overlapsBy nodeBytes oenv lin lout =
  case (resolveOffset lin oenv, resolveOffset lout oenv) of
    ((rootIn, offIn), (rootOut, offOut))
      | rootIn == rootOut -> let gap = offIn - offOut
                              in gap >= 0 && gap < nodeBytes
    _ -> False

tagGap :: OffEnv -> LocVar -> LocVar -> Int
tagGap oenv lin lout =
  snd (resolveOffset (getDconLoc lin) oenv) - snd (resolveOffset (getDconLoc lout) oenv)

removeCopies :: Prog2 -> PassM Prog2
removeCopies Prog{ddefs,fundefs,mainExp} = do
  dflags <- getDynFlags
  let keepCopiesForMutableGC = gopt Opt_UseMutableCursors dflags && not (gopt Opt_DisableGC dflags)
  ddefs' <- mapM (\ddf@DDef{dataCons} -> do
                    dcon <- fromVar <$> gensym (toVar indirectionTag)
                    -- RemoveCopies might run more than once (b/c repairProgram), so
                    -- we ensure that we add the Indirection constructor only once.
                    let datacons = filter (not . isIndirectionTag . fst) dataCons
                    let ty_of_indirection = getCursorTypeForDataCon ddefs ddf  
                    return ddf {dataCons = datacons ++ [(dcon, [(False, ty_of_indirection)])]} )
            ddefs
  -- Don't process copy* functions
  fds' <- mapM (\fn -> if isCopyFunName (funName fn)
                       then return fn
                       else removeCopiesFn keepCopiesForMutableGC ddefs' fundefs fn)
               (M.elems fundefs)
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
      env2 = Env2 M.empty (initFunEnv fundefs)
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (mn, ty) -> Just . (,ty) <$>
                  removeCopiesExp keepCopiesForMutableGC ddefs' fundefs M.empty M.empty env2 mn
  let prg' = Prog ddefs' fundefs' mainExp'
  -- See Note [A factored indirection lives in the tag buffer].
  if gopt Opt_GenGc dflags && not (gopt Opt_DisableGC dflags)
       && writesFactoredIndirections isSoALoc prg'
    then error $ "\nGibbon cannot share a fully-factored (SoA) value under --gen-gc: the"
                 ++ " generational collector has no write barrier for a factored indirection."
                 ++ " Use the default collector or --no-gc.\n"
    else return prg'

removeCopiesFn :: Bool -> DDefs Ty2 -> FunDefs2 -> FunDef2 -> PassM FunDef2
removeCopiesFn keepCopiesForMutableGC ddefs fundefs f@FunDef{funArgs,funTy,funBody} = do
  let initLocEnv = M.fromList $ map (\(LRM lc r _) -> case r of 
                                                          _ -> (lc, regionToVar r)
                                    ) (locVars funTy)
      initTyEnv  = M.fromList $ zip funArgs (arrIns funTy)
      env2 = Env2 initTyEnv (initFunEnv fundefs)
  bod' <- removeCopiesExp keepCopiesForMutableGC ddefs fundefs initLocEnv M.empty env2 funBody
  return $ f {funBody = bod'}

-- | Note [A value cannot be re-placed onto itself]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- When two constructor alternatives consume the SAME let-bound packed value and
-- their field layouts differ, the value's start is not where both need it.
-- Location inference's copy repair fires, and neither mechanism implementing
-- that copy works when the destination overlaps the value:
--
--   * as an INDIRECTION (the default): the node is 9 bytes -- a tag plus a
--     tagged pointer -- written AT the destination pointing AT the value, so if
--     the value begins fewer than 9 bytes later the pointer field runs over the
--     value's own tag.  It is the distance, not the shape, that matters: the
--     same program is correct once the gap reaches 16.
--   * as a REAL COPY (what @--use-mutable-cursors@ keeps): the copy walks
--     forward writing into storage it is still reading, for the same reason.
--
-- This is a property of the representation, not of either lowering, so the
-- response is to refuse before code generation.  A non-overlapping re-placement
-- is untouched and still becomes an indirection.
--
-- Fully-factored (SoA) values follow the same rule, applied to the tag buffer
-- only; see Note [A factored indirection lives in the tag buffer].

-- | Note [A factored indirection lives in the tag buffer]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- An SoA value's start is one cursor per buffer.  Its indirection is written
-- into the TAG buffer only: tag 'indirectionTag' followed by the target's N
-- cursors (N = 'locBufferCount', nested factored fields included), 8 bytes
-- each, untagged, in 'linearizeLocVar' order.  Every field buffer is left
-- untouched, so the indirection's end witness is the tag cursor advanced by
-- 1 + 8N and every field cursor unchanged.  GC on and off use the same bytes;
-- with GC on, Cursorize also records one region reference per target buffer.
--
-- Only the tag buffer is written, so only the tag-buffer distance can make the
-- node overwrite the value it points at.  That happens for a shared tail
-- consumed by two constructor alternatives: each alternative writes one tag
-- before it, so the two tag cursors coincide while the field cursors differ,
-- and no in-place node can say "same tag, other fields".  Such a re-placement
-- is refused.  Any other SoA re-placement becomes an indirection, also under
-- @--use-mutable-cursors@, where AoS keeps the copy: the kept SoA copy's ABI
-- does not typecheck (@CursorArrayTy n <> CursorTy@).

replaceUnsupported :: String -> Exp2 -> LocVar -> LocVar -> a
replaceUnsupported why arg lin lout =
  error $
    "\nGibbon cannot re-place this packed value: " ++ why ++ ".\n\n"
    ++ "  the value    : " ++ sdoc arg ++ "\n"
    ++ "  currently at : " ++ sdoc lin ++ "\n"
    ++ "  required at  : " ++ sdoc lout ++ "\n\n"
    ++ "Two constructor alternatives need this value at different places, so a copy\n"
    ++ "was required, and the copy cannot be expressed: the destination overlaps the\n"
    ++ "value's own storage, so both an indirection node and a real copy would write\n"
    ++ "over the value they are re-placing.\n\n"
    ++ "This normally comes from a let-bound packed value consumed by more than one\n"
    ++ "constructor alternative:\n\n"
    ++ "    let rst = mkT (n - 1)\n"
    ++ "     in if p then A x rst else B y rst\n\n"
    ++ "Write the producing call inside each alternative instead:\n\n"
    ++ "    if p then A x (mkT (n - 1)) else B y (mkT (n - 1))\n\n"
    ++ "For an array-of-structs type ({-# ANN type T \"Linear\" #-}) the alternatives\n"
    ++ "must also agree on where the packed field starts, or be far enough apart that\n"
    ++ "an indirection fits between them.  For a fully-factored type\n"
    ++ "({-# ANN type T \"Factored\" #-}) the indirection is written into the tag\n"
    ++ "buffer only, so it is the alternatives' tag-buffer positions that must be far\n"
    ++ "enough apart; when each alternative writes one tag before the shared value\n"
    ++ "they coincide.\n"

-- | Why, if at all, this re-placement cannot be expressed.
--
-- @keepCopies@ says the copy will survive as a real @_copy_T@ call rather than
-- becoming an indirection (see 'removeCopies': that is the
-- @--use-mutable-cursors@ path).  The two lowerings fail under different
-- conditions, so the rule is different for each:
--
--   * as an indirection, only an OVERLAPPING re-placement is wrong -- the
--     9-byte node would be written over the value it points at.  A
--     re-placement further away is fine, and 'tests/vw31/gap16.hs.in' is the
--     control proving it still compiles and runs;
--   * as a kept copy, a same-region re-placement is wrong regardless of the
--     distance.  Measured on that same gap16 fixture with
--     @--use-mutable-cursors@: the value comes back with an unknown tag at
--     every depth above two, while the identical program on the indirection
--     path is correct.  Refuse rather than emit a value already measured to
--     be corrupt.
--
-- Neither rule fires on anything in the tree: across 199 programs
-- (examples/, examples/soa_examples/programs/{AOS,SOA}) compiled with mutable
-- cursors there is no same-region re-placement at all, and across the 109 SoA
-- programs under @--packed@ there is no SoA copy.
unsupportedReplacement :: Bool -> OffEnv -> LocVar -> LocVar -> Maybe String
unsupportedReplacement keepCopies oenv lin lout
  | isSoALoc lin /= isSoALoc lout =
      Just "one location is fully factored (SoA) and the other is not"
  | isSoALoc lin
  , overlapsBy (soaIndirectionTagBytes lin) oenv (getDconLoc lin) (getDconLoc lout) =
      Just ("it is fully factored (SoA), and its tag-buffer start is only "
            ++ show (tagGap oenv lin lout)
            ++ " bytes after the destination's, while a factored indirection needs "
            ++ show (soaIndirectionTagBytes lin) ++ " bytes of the tag buffer")
  | isSoALoc lin = Nothing
  | replacementOverlaps oenv lin lout =
      Just ("the destination is only "
            ++ show (snd (resolveOffset lin oenv) - snd (resolveOffset lout oenv))
            ++ " bytes before the value itself, and an indirection needs "
            ++ show indirectionBytes)
  | keepCopies && sameRegion oenv lin lout =
      Just ("it would have to be copied within one region, which the copy ABI"
            ++ " kept for mutable cursors does not implement correctly")
  | otherwise = Nothing

sameRegion :: OffEnv -> LocVar -> LocVar -> Bool
sameRegion oenv lin lout =
  fst (resolveOffset lin oenv) == fst (resolveOffset lout oenv)

-- ASSUMPTION: copy functions would always be called on a single argument.
removeCopiesExp :: Bool -> DDefs Ty2 -> FunDefs2 -> LocEnv -> OffEnv -> Env2 Var Ty2 -> Exp2 -> PassM Exp2
removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv oenv env2 ex =
  case ex of
    -- See Note [A factored indirection lives in the tag buffer].  This must come
    -- before every other copy case, including the ones that keep copies for
    -- mutable-cursor GC, so that the refusal is what the user sees rather than
    -- a downstream type error or a fault at run time.
    AppE f _cty [lin,lout] [arg]
      | isCopyFunName f, lin /= lout
      , Just why <- unsupportedReplacement keepCopiesForMutableGC oenv lin lout ->
      replaceUnsupported why arg lin lout

    LetE (_,_,PackedTy{}, (AppE f _cty [lin,lout] [arg])) _
      | isCopyFunName f, lin /= lout
      , Just why <- unsupportedReplacement keepCopiesForMutableGC oenv lin lout ->
      replaceUnsupported why arg lin lout

    AppE f _cty [lin,_] [_] | isCopyFunName f && keepCopiesForMutableGC && not (isSoALoc lin) ->
      pure ex

    LetE (v,locs,ty, rhs@(AppE f _cty [lin,_] [_])) bod
      | isCopyFunName f && keepCopiesForMutableGC && not (isSoALoc lin) ->
      LetE (v,locs,ty, rhs) <$>
        removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv oenv (extendVEnv v ty env2) bod

    -- Note [An identity copy is not an indirection]
    -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    -- A copy whose source and destination are the SAME location is the
    -- identity: the value already sits at the destination, so there is nothing
    -- to move and nothing to point at.  Rewriting it to an indirection is not
    -- identity-preserving -- it writes an indirection node AT the value,
    -- pointing AT itself, which both destroys the value and creates a cycle.
    -- The RTS write barrier walks indirection chains
    -- (@gib_indirection_barrier@), so the cycle is a hang; a traversal that
    -- reaches the clobbered node instead reports an unknown tag or faults.
    --
    -- 'InferLocations' produces such a copy for
    --
    --     let rst = mkT (n-1)
    --      in if n < 3 then A n rst else B (n+200) rst
    --
    -- because each constructor arm allocates its own fresh field location and
    -- the unification of the second arm's location with @rst@'s fails, so the
    -- copy repair tactic fires.  The two locations then turn out to denote the
    -- same address -- both are @loc + 1 + 8@ -- and later location
    -- simplification substitutes them to a single variable, leaving
    -- @_copy_T [l, l] rst@.  The redundant copy is a missed optimization; the
    -- self-indirection was a miscompilation.
    --
    -- Emitting the argument unchanged is correct for exactly the reason above:
    -- @lin == lout@ means the result location is where the argument already
    -- lives, so the copy's result IS the argument.
    AppE f _cty [lin,lout] [arg] | isCopyFunName f && lin == lout ->
      pure arg

    -- This AppE copies data from 'lin' to 'lout'. When this becomes an
    -- indirection node, 'lout' is the _pointer_, and 'lin' the _pointee_.
    AppE f _cty [lin,lout] [arg] | isCopyFunName f -> do
      indirection <- gensym "indirection"
      let (PackedTy tycon _) = gRecoverType ddefs env2 ex
          -- the indirection datacon for this type
          indrDcon = filter isIndirectionTag $ getConOrdering ddefs tycon
      case indrDcon of
        [] -> error $ "removeCopies: No indirection constructor found for: " ++ sdoc tycon
        [dcon] -> do
          let reg_lout = case (lenv # lout) of 
                                  SingleR v -> fromRegVarToLocVar $ (SingleR v)
                                  r@(SoARv _ _) -> fromRegVarToLocVar r
          let reg_lin = case (lenv # lin) of 
                                  SingleR v -> fromRegVarToLocVar $ (SingleR v)
                                  r@(SoARv _ _) -> fromRegVarToLocVar r
          return $
            mkLets ([(indirection,[],PackedTy tycon lout,
                      Ext $ IndirectionE tycon dcon (lout , reg_lout) (lin, reg_lin) arg)])
            (VarE indirection)
        oth -> error $ "removeCopies: Multiple indirection constructors: " ++ sdoc oth

    -- See Note [An identity copy is not an indirection].  The binding is
    -- substituted away rather than rebound: @cpy@ and its argument denote the
    -- same value at the same location, and leaving a packed @let cpy = rst@
    -- behind would ask Cursorize to produce a fresh (start, end) witness pair
    -- for a value that already has one.
    LetE (v,_locs,_ty@(PackedTy _ _), (AppE f _cty [lin,lout] [arg@VarE{}])) bod
      | isCopyFunName f && lin == lout ->
      removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv oenv env2
        (gSubstE (VarE v) arg bod)

    LetE (v,locs,ty@(PackedTy tycon _), (AppE f _cty [lin,lout] [arg])) bod | isCopyFunName f -> do
      -- Get the indirection datacon for this type
      let indrDcon = filter isIndirectionTag $ getConOrdering ddefs tycon
      case indrDcon of
        [] -> error $ "removeCopies: No indirection constructor found for: " ++ sdoc tycon
        [dcon] -> do
          let reg_lout = case (lenv # lout) of 
                                  SingleR vr -> fromRegVarToLocVar $ (SingleR vr)
                                  r@(SoARv _ _) -> fromRegVarToLocVar r
          let reg_lin = case (lenv # lin) of 
                                  SingleR vr -> fromRegVarToLocVar $ (SingleR vr)
                                  r@(SoARv _ _) -> fromRegVarToLocVar r
          LetE (v,locs,ty, Ext $ IndirectionE tycon dcon (lout , reg_lout) (lin, reg_lin) arg) <$>
            removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv oenv (extendVEnv v ty env2) bod
        oth -> error $ "removeCopies: Multiple indirection constructors: " ++ sdoc oth

    Ext ext ->
      case ext of
        -- Update lenv with a binding for loc
        LetLocE loc FreeLE bod -> do
          Ext <$> LetLocE loc FreeLE <$>
            removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv oenv env2 bod
        StartOfPkdCursor cur -> pure $ Ext $ StartOfPkdCursor cur
        TagCursor a b -> pure $ Ext $ TagCursor a b
        LetLocE loc rhs bod -> do
          let reg = case rhs of
                      StartOfRegionLE r  -> regionToVar r
                      InRegionLE r -> regionToVar r
                      AfterConstantLE _ lc   -> lenv # lc
                      AfterVariableLE _ lc _ -> lenv # lc
                      FromEndLE lc           -> lenv # lc -- TODO: This needs to be fixed
                      GetDataConLocSoA lc -> 
                        let rlc = lenv # lc
                         in getDataConRegFromRegVar rlc
                      GetFieldLocSoA (dcon, idx) lc -> 
                        let rlc = lenv # lc
                         in getFieldRegFromRegVar (dcon, idx) rlc 
                      AssignLE lc -> lenv # lc
                      GenSoALoc dconLoc fieldLocs -> 
                         let dconReg = lenv # dconLoc
                             fldRegs = map (\((dcon, idx), fl) -> let rl = lenv # fl
                                                                   in ((dcon, idx), rl)
                                           ) fieldLocs
                           in SoARv dconReg fldRegs
          Ext <$> LetLocE loc rhs <$>
            removeCopiesExp keepCopiesForMutableGC ddefs fundefs (M.insert loc reg lenv) (learnOffset loc rhs oenv) env2 bod
       -- Straightforward recursion
        RetE{} -> return ex
        AddFixed{} -> return ex
        LetRegionE r sz endmut ty bod -> Ext <$> LetRegionE r sz endmut ty <$> go bod
        LetParRegionE r sz ty bod -> Ext <$> LetParRegionE r sz ty <$> go bod
        FromEndE{}       -> return ex
        BoundsCheck{}    -> return ex
        IndirectionE{}   -> return ex
        GetCilkWorkerNum -> return ex
        LetAvail vs bod -> Ext <$> LetAvail vs <$> go bod
        AllocateTagHere{} -> return ex
        AllocateScalarsHere{} -> return ex
        SSPush{} -> return ex
        SSPop{} -> return ex

    -- Straightforward recursion
    VarE{}     -> return ex
    LitE{}     -> return ex
    CharE{}    -> return ex
    FloatE{}   -> return ex
    LitSymE{}  -> return ex
    AppE{}     -> return ex
    PrimAppE{} -> return ex
    DataConE{} -> return ex
    ProjE i e  -> ProjE i <$> go e
    IfE a b c  -> IfE <$> go a <*> go b <*> go c
    MkProdE ls -> MkProdE <$> mapM go ls
    LetE (v,locs,ty, rhs) bod ->
      LetE <$> (v,locs,ty,) <$> go rhs <*>
        removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv oenv (extendVEnv v ty env2) bod
    CaseE scrt mp -> do
      let (VarE v) = scrt
          PackedTy _ tyloc = lookupVEnv v env2
          reg = lenv M.! tyloc
      CaseE scrt <$> mapM (docase reg lenv env2) mp
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    WithArenaE v e -> do
      e' <- go e
      return $ WithArenaE v e'
    SpawnE{}-> pure ex
    SyncE   -> pure ex
    MapE{}  -> error $ "go: TODO MapE"
    FoldE{} -> error $ "go: TODO FoldE"
  where
    go = removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv oenv env2
    docase reg lenv1 env21 (dcon,vlocs,bod) = do
      -- Update the envs with bindings for pattern matched variables and locations.
      -- The locations point to the same region as the scrutinee.
      let (vars,locs) = unzip vlocs
          lenv1' = foldr (\lc acc -> M.insert lc reg acc) lenv1 locs
          env21' = extendPatternMatchEnv dcon ddefs vars locs env21
      (dcon,vlocs,) <$> (removeCopiesExp keepCopiesForMutableGC ddefs fundefs lenv1' oenv env21' bod)
