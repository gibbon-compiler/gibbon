module Gibbon.Passes.Cursorize
  (cursorize) where

import           Control.Monad (forM)
import qualified Data.List as L
import qualified Data.Map as M
import           Data.Maybe (fromJust)
import           Text.PrettyPrint.GenericPretty

import           Gibbon.DynFlags
import           Gibbon.Common
import           Gibbon.L2.Syntax
import           Gibbon.L3.Syntax hiding ( BoundsCheck, RetE, GetCilkWorkerNum, LetAvail,
                                           AllocateTagHere, AllocateScalarsHere, SSPush, SSPop )
import qualified Gibbon.L3.Syntax as L3
import           Gibbon.Passes.AddRAN ( numRANsDataCon )

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

Every packed input becomes a read cursor. And it takes additional output cursors
for every packed type in the return value. Every packed return value becomes a
(Cursor,Cursor) i.e (start,end). And it returns additional end_of_read cursors
if the functions "traverses" it's input (more details in the paer).

-}


-- | Track variables depending on location variables.
--
--   If we have to create binding of the form `let v = loc` (in case expressions for example),
--   but `loc` is not bound yet, we'll add the variable to this map.
--   This is a stupid/simple way to get rid of FindWitnesses.
--   See `FindWitnesses.hs` for why that is needed.
type DepEnv = M.Map LocVar [(Var,[()],Ty3,Exp3)]

-- | Things we cannot define until we see a join point. There's a Ty2 to so that
-- we can extend the environment.
type SyncEnv = M.Map Var [(Var,[()],Ty3,Ty2,Exp3)]

-- |
cursorize :: Prog2 -> PassM Prog3
cursorize Prog{ddefs,fundefs,mainExp} = do
  fns' <- mapM (cursorizeFunDef ddefs fundefs . snd) (M.toList fundefs)
  let fundefs' = M.fromList $ L.map (\f -> (funName f, f)) fns'
      ddefs'   = M.map eraseLocMarkers ddefs
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (e,ty) -> do
                  if hasPacked ty
                  then Just . (, stripTyLocs ty) <$>
                         fromDi <$> cursorizePackedExp ddefs fundefs M.empty M.empty M.empty e
                  else Just . (,stripTyLocs ty) <$>
                         cursorizeExp ddefs fundefs M.empty M.empty M.empty e
  pure (Prog ddefs' fundefs' mainExp')

-- |
cursorizeFunDef :: DDefs Ty2 -> FunDefs2 -> FunDef2 -> PassM FunDef3
cursorizeFunDef ddefs fundefs FunDef{funName,funTy,funArgs,funBody,funRec,funInline} = do
  let inLocs  = inLocVars funTy
      outLocs = outLocVars funTy
      outRegs = outRegVars funTy
      inRegs  = inRegVars funTy
      in_tys  = arrIns funTy
      out_ty  = arrOut funTy
      funTy'  = cursorizeArrowTy funTy

      -- [2019.03.04] CSK: the order of these new cursor/region arguments isn't
      -- intuitive and can be improved.

      -- Input & output regions are always inserted before all other arguments.
      regBinds = map toEndV (inRegs ++ outRegs)

      -- Output cursors after that.
      outCurBinds = outLocs

      -- Then the input cursors. Bind an input cursor for every packed argument.
      inCurBinds = case inLocs of
                     [] -> mkLets []
                     _  ->
                           let projs = concatMap (uncurry mkInProjs) (zip (map VarE funArgs) in_tys)
                               bnds  = [(loc,[],CursorTy,proj) | (loc,proj) <- zip inLocs projs]
                           in mkLets bnds

      initTyEnv = M.fromList $ (map (\(a,b) -> (a,cursorizeInTy b)) $ zip funArgs in_tys) ++
                               [(a,CursorTy) | (LRM a _ _) <- locVars funTy]

      funargs = regBinds ++ outCurBinds ++ funArgs

  bod <- if hasPacked out_ty
         then fromDi <$> cursorizePackedExp ddefs fundefs M.empty initTyEnv M.empty funBody
         else cursorizeExp ddefs fundefs M.empty initTyEnv M.empty funBody
  let bod' = inCurBinds bod
      fn = FunDef funName funargs funTy' bod' funRec funInline
  return fn

  where
    -- | The only difference between this and L3.cursorizeTy is that here,
    --   packed types are replaced by a single CursorTy instead of
    --   a tuple (CursorTy,CursorTy). This is because only `start` cursors are
    --   passed in for packed function arguments.
    cursorizeInTy :: UrTy a -> UrTy b
    cursorizeInTy ty =
      case ty of
        IntTy     -> IntTy
        FloatTy   -> FloatTy
        SymTy     -> SymTy
        BoolTy    -> BoolTy
        ProdTy ls -> ProdTy $ L.map cursorizeInTy ls
        SymDictTy ar _ty -> SymDictTy ar CursorTy
        PDictTy k v -> PDictTy (cursorizeInTy k) (cursorizeInTy v)
        PackedTy{}    -> CursorTy
        VectorTy el_ty -> VectorTy $ cursorizeInTy el_ty
        ListTy el_ty -> ListTy $ cursorizeInTy el_ty
        PtrTy -> PtrTy
        CursorTy  -> CursorTy
        ArenaTy   -> ArenaTy
        SymSetTy  -> SymSetTy
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
    mkInProjs = go []
     where
       go acc e ty =
         case ty of
           PackedTy{} -> acc ++ [e]
           ProdTy tys -> L.foldl (\acc2 (ty',n) -> go acc2 (mkProj n e) ty')
                                 acc (zip tys [0..])
           _ -> acc

    cursorizeArrowTy :: ArrowTy2 -> ([Ty3] , Ty3)
    cursorizeArrowTy ty@ArrowTy2{arrIns,arrOut,locVars,locRets} =
      let
          -- Regions corresponding to ouput cursors. (See [Threading regions])
          numOutRegs = length (outRegVars ty)
          outRegs = L.map (\_ -> CursorTy) [1..numOutRegs]

          -- Adding additional outputs corresponding to end-of-input-value witnesses
          -- We've already computed additional location return value in RouteEnds
          ret_curs = L.map (\_ -> CursorTy) locRets
          out_curs = outRegs ++ ret_curs
          out_ty = case out_curs of
                     [] -> arrOut
                     _  -> ProdTy $ out_curs ++ [arrOut]

          -- Packed types in the output then become end-cursors for those same destinations.
          newOut = mapPacked (\_ _ -> ProdTy [CursorTy, CursorTy]) out_ty

          newOut' = case newOut of
                      SymDictTy a _ -> SymDictTy a CursorTy
                      _ -> newOut

          -- Adding additional input arguments for the destination cursors to which outputs
          -- are written.
          outCurs   = filter (\(LRM _ _ m) -> m == Output) locVars
          outCurTys = map (\_ -> CursorTy) outCurs
          inRegs    = map (\_ -> CursorTy) (inRegVars ty)
          in_tys    = inRegs ++ outRegs ++ outCurTys ++ arrIns

          -- Packed types in the input now become (read-only) cursors.
          newIns    = map (constPacked CursorTy) in_tys

      in (map stripTyLocs newIns, stripTyLocs newOut')


-- | Cursorize expressions NOT producing `Packed` values
cursorizeExp :: DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> SyncEnv -> Exp2
             -> PassM Exp3
cursorizeExp ddfs fundefs denv tenv senv ex =
  case ex of
    VarE v    -> return $ VarE v
    LitE n    -> return $ LitE n
    FloatE n  -> return $ FloatE n
    LitSymE n -> return $ LitSymE n

    AppE{} -> cursorizeAppE ddfs fundefs denv tenv senv ex

    PrimAppE RequestEndOf [arg] -> do
      let (VarE v) = arg
      return $ VarE (toEndV v)

    PrimAppE RequestSizeOf [arg] -> do
      let (VarE v) = arg
      case M.lookup v tenv of
        Nothing -> error $ "cursorizeExp: Unbound variable: " ++ sdoc v
        Just ty -> if isPackedTy ty
                   then pure $ Ext $ SubPtr (toEndV v) v
                   else pure $ LitE $ fromJust $ sizeOfTy ty

    PrimAppE pr args -> PrimAppE (toL3Prim pr) <$> mapM go args

    LetE (v,_locs, _ty, (PrimAppE (ReadPackedFile path tyc reg ty2) [])) bod ->
      cursorizeReadPackedFile ddfs fundefs denv tenv senv True v path tyc reg ty2 bod

    LetE (_v,_locs,_ty, (MkProdE _ls)) _bod ->
      cursorizeProd False ddfs fundefs denv tenv senv ex

    LetE (_v,_locs, ty, ProjE{}) _bod | isPackedTy ty ->
       cursorizeProj False ddfs fundefs denv tenv senv ex

    LetE (_v,_locs, _ty, SpawnE{}) _bod ->
      cursorizeSpawn False ddfs fundefs denv tenv senv ex

    LetE (_v,_locs, _ty, SyncE) _bod ->
      cursorizeSync False ddfs fundefs denv tenv senv ex

    LetE (v,_locs,ty, rhs@(Ext (SSPush _ start _ _))) bod ->
      case M.lookup start tenv of
        Nothing -> go bod
        Just{}  -> do
          rhs' <- go rhs
          bod' <- go bod
          let ty' = cursorizeTy ty
          return $ LetE (v,[],ty',rhs') bod'

    LetE (v,_locs,ty, rhs@(Ext (SSPop _ start _))) bod ->
      case M.lookup start tenv of
        Nothing -> go bod
        Just{}  -> do
          rhs' <- go rhs
          bod' <- go bod
          let ty' = cursorizeTy ty
          return $ LetE (v,[],ty',rhs') bod'

    LetE bnd bod -> cursorizeLet False ddfs fundefs denv tenv senv bnd bod

    IfE a b c  -> IfE <$> go a <*> go b <*> go c

    MkProdE ls -> MkProdE <$> mapM go ls

    ProjE i e  -> ProjE i <$> go e

    -- Eg. leftmost
    CaseE scrt brs -> do
      -- ASSUMPTION: scrt is flat
      let (VarE  v) = scrt
      CaseE (VarE $ v) <$>
        mapM (unpackDataCon ddfs fundefs denv tenv senv False v) brs

    DataConE _ _ _ -> error $ "cursorizeExp: Should not have encountered DataConE if type is not packed: "++ndoc ex

    TimeIt e ty b -> TimeIt <$> go e <*> pure (stripTyLocs ty) <*> pure b

    WithArenaE v e -> do
      e' <- cursorizeExp ddfs fundefs denv (M.insert v ArenaTy tenv) senv e
      return $ WithArenaE v e'

    SpawnE{} -> error "cursorizeExp: Unbound SpawnE"
    SyncE{}  -> error "cursorizeExp: Unbound SyncE"

    -- Eg. leftmost
    Ext ext ->
      case ext of
        AddFixed v i -> return $ Ext $ L3.AddCursor v (L3.LitE i)
        RetE locs v ->
          case locs of
              [] -> return (VarE v)
              _  -> return $ L3.MkProdE $ [VarE loc | loc <- locs] ++ [VarE v]

        -- All locations are transformed into cursors here. Location arithmetic
        -- is expressed in terms of corresponding cursor operations.
        -- See `cursorizeLocExp`
        LetLocE loc rhs bod -> do
          let rhs_either = cursorizeLocExp denv tenv senv loc rhs
              (bnds,tenv') = case M.lookup loc denv of
                               Nothing -> ([],tenv)
                               Just vs -> let extended = M.fromList [ (v,CursorTy) | (v,_,CursorTy,_) <- vs]
                                          in (vs, M.union extended tenv)
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
            Right (rhs', bnds', tenv'', senv') -> do
              let tenv''' = M.union tenv' tenv''
              case rhs of
                FromEndLE{} ->
                  if isBound loc tenv
                  then cursorizeExp ddfs fundefs denv (M.insert loc CursorTy tenv''') senv' bod
                  -- Discharge bindings that were waiting on 'loc'.
                  else mkLets (bnds' ++ [(loc,[],CursorTy,rhs')] ++ bnds) <$>
                         cursorizeExp ddfs fundefs denv (M.insert loc CursorTy tenv''') senv' bod
                -- Discharge bindings that were waiting on 'loc'.
                _ -> mkLets (bnds' ++ [(loc,[],CursorTy,rhs')] ++ bnds) <$>
                       cursorizeExp ddfs fundefs denv (M.insert loc CursorTy tenv''') senv bod
            Left denv' -> cursorizeExp ddfs fundefs denv' tenv' senv bod

        -- Exactly same as cursorizePackedExp
        LetRegionE reg _ _ bod -> do
          mkLets (regionToBinds False reg) <$> go bod

        LetParRegionE reg _ _ bod -> do
          mkLets (regionToBinds True reg) <$> go bod

        BoundsCheck i bound cur -> return $ Ext $ L3.BoundsCheck i bound cur

        FromEndE{} -> error $ "cursorizeExp: TODO FromEndE" ++ sdoc ext

        IndirectionE{} -> error $ "cursorizeExp: Unexpected IndirectionE"

        GetCilkWorkerNum -> return $ Ext $ L3.GetCilkWorkerNum

        LetAvail vs bod  -> Ext <$> L3.LetAvail vs <$> go bod

        AllocateTagHere v tycon -> pure $ Ext $ L3.AllocateTagHere v tycon

        AllocateScalarsHere v -> pure $ Ext $ L3.AllocateScalarsHere v

        SSPush a b c d -> pure $ Ext $ L3.SSPush a b c d
        SSPop a b c -> pure $ Ext $ L3.SSPop a b c

    MapE{} -> error $ "TODO: cursorizeExp MapE"
    FoldE{} -> error $ "TODO: cursorizeExp FoldE"

  where
    go = cursorizeExp ddfs fundefs denv tenv senv


-- Cursorize expressions producing `Packed` values
cursorizePackedExp :: DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> SyncEnv -> Exp2
                   -> PassM (DiExp Exp3)
cursorizePackedExp ddfs fundefs denv tenv senv ex =
  case ex of
    -- Here the allocation has already been performed:
    -- To follow the calling convention, we are reponsible for tagging on the
    -- end here:
    VarE v -> do
      let ty = case M.lookup v tenv of
                 Just t -> t
                 Nothing -> error $ sdoc v ++ " not found."
      if isPackedTy ty
      then return $ mkDi (VarE v) [ VarE (toEndV v) ]
      else return $ dl $ VarE v

    LitE _n    -> error $ "Shouldn't encounter LitE in packed context:" ++ sdoc ex
    FloatE{}   -> error $ "Shouldn't encounter FloatE in packed context:" ++ sdoc ex
    LitSymE _n -> error $ "Shouldn't encounter LitSymE in packed context:" ++ sdoc ex

    AppE{} -> dl <$> cursorizeAppE ddfs fundefs denv tenv senv ex

    -- DictLookup returns a packed value bound to a free location.
    -- PrimAppE (DictLookupP (PackedTy _ ploc)) vs ->
    --     do vs' <- forM vs $ \v -> cursorizeExp ddfs fundefs denv tenv v
    --        return $ mkDi (PrimAppE (DictLookupP CursorTy) vs') [ Ext NullCursor ]

    PrimAppE _ _ -> error $ "cursorizePackedExp: unexpected PrimAppE in packed context:" ++ sdoc ex

    -- The only (other) primitive that returns packed data is ReadPackedFile:
    -- This is simpler than TimeIt below.  While it's out-of-line,
    -- it doesn't need memory allocation (NewBuffer/ScopedBuffer).
    -- This is more like the witness case below.
    LetE (v,_locs, _ty, (PrimAppE (ReadPackedFile path tyc reg ty2) [])) bod ->
       Di <$> cursorizeReadPackedFile ddfs fundefs denv tenv senv True v path tyc reg ty2 bod

    LetE (v,_locs,_ty, (PrimAppE (DictLookupP (PackedTy _ ploc)) vs)) bod ->
        do vs' <- forM vs $ \w -> cursorizeExp ddfs fundefs denv tenv senv w
           let bnd = mkLets [(ploc, [], CursorTy, (PrimAppE (DictLookupP CursorTy) vs'))
                            ,(v, [], CursorTy, VarE ploc)]
               tenv' = M.insert ploc CursorTy $ M.insert v CursorTy tenv
           onDi bnd <$> go tenv' senv bod

    LetE (_v,_locs,_ty, (MkProdE _ls)) _bod ->
      dl <$> cursorizeProd True ddfs fundefs denv tenv senv ex

    LetE (_v,_locs,ty, ProjE{}) _bod | isPackedTy ty ->
      dl <$> cursorizeProj True ddfs fundefs denv tenv senv ex


    MkProdE ls -> do
      let tys = L.map (gRecoverType ddfs (Env2 tenv M.empty)) ls
      es <- forM (zip tys ls) $ \(ty,e) -> do
              case ty of
                  _ | isPackedTy ty -> fromDi <$> cursorizePackedExp ddfs fundefs denv tenv senv e
                  _ -> cursorizeExp ddfs fundefs denv tenv senv e
      let rhs' = MkProdE es
      return $ Di rhs'

    -- Not sure if we need to replicate all the checks from Cursorize1
    ProjE i e -> dl <$> ProjE i <$> fromDi <$> go tenv senv e

    LetE (_v,_locs, _ty, SpawnE{}) _bod ->
      dl <$> cursorizeSpawn True ddfs fundefs denv tenv senv ex

    LetE (_v,_locs, _ty, SyncE) _bod ->
      dl <$> cursorizeSync True ddfs fundefs denv tenv senv ex

    LetE (v,_locs,ty, rhs@(Ext (SSPush _ start _ _))) bod ->
      case M.lookup start tenv of
        Nothing -> go tenv senv bod
        Just{}  -> do
          rhs' <- go tenv senv rhs
          let ty' = cursorizeTy ty
          bod' <- go (M.insert v ty tenv) senv bod
          return $ Di (LetE (v,[], ty', fromDi rhs') (fromDi bod'))

    LetE (v,_locs,ty, rhs@(Ext (SSPop _ start _))) bod ->
      case M.lookup start tenv of
        Nothing -> go tenv senv bod
        Just{}  -> do
          rhs' <- go tenv senv rhs
          let ty' = cursorizeTy ty
          bod' <- go (M.insert v ty tenv) senv bod
          return $ Di (LetE (v,[],ty', fromDi rhs') (fromDi bod'))

    LetE bnd bod -> dl <$> cursorizeLet True ddfs fundefs denv tenv senv bnd bod

    -- Here we route the dest cursor to both braches.  We switch
    -- back to the other mode for the (non-packed) test condition.
    IfE a b c -> do
      Di b' <- go tenv senv b
      Di c' <- go tenv senv c
      a'    <- cursorizeExp ddfs fundefs denv tenv senv a
      return $ Di $ IfE a' b' c'

    -- A case expression is eventually transformed into a ReadTag + switch stmt.
    -- We first retrieve the cursor referred to by the scrutinee, and unpack
    -- the first bound variable 1 byte after that cursor. Thats all we need to do
    -- here, because we've already computed other locations in InferLocations and
    -- RouteEnds
    CaseE scrt brs -> do
      -- ASSUMPTION: scrutinee is always flat
      let (VarE v) = scrt
      dl <$>
        CaseE (VarE $ v) <$>
          mapM (unpackDataCon ddfs fundefs denv tenv senv True v) brs

    DataConE sloc dcon args -> do
      let
          -- Return (start,end) cursors
          -- The final return value lives at the position of the out cursors:
          go2 :: Bool -> Var -> [(Exp2, Ty2)] -> PassM Exp3
          go2 marker_added d [] =
            if not (marker_added)
            then do
              end_scalars_alloc <- gensym "end_scalars_alloc"
              return (LetE (end_scalars_alloc,[],ProdTy [],Ext $ EndScalarsAllocation sloc)
                           (MkProdE [VarE sloc, VarE d]))
            else return (MkProdE [VarE sloc, VarE d])

          go2 marker_added d ((rnd, ty):rst) = do
            d' <- gensym "writecur"
            case ty of
              _ | isPackedTy ty -> do

                 rnd' <- go tenv senv rnd
                 end_scalars_alloc <- gensym "end_scalars_alloc"
                 (if not marker_added
                  then LetE (end_scalars_alloc,[],ProdTy [],Ext $ EndScalarsAllocation sloc)
                  else id) <$>
                   LetE (d',[], CursorTy, projEnds rnd') <$>
                   go2 True d' rst

              -- Int, Float, Sym, or Bool
              _ | isScalarTy ty -> do
                rnd' <- cursorizeExp ddfs fundefs denv tenv senv rnd
                LetE (d',[], CursorTy, Ext $ WriteScalar (mkScalar ty) d rnd') <$>
                  go2 marker_added d' rst

              -- Write a pointer to a vector
              VectorTy el_ty -> do
                rnd' <- cursorizeExp ddfs fundefs denv tenv senv rnd
                LetE (d',[], CursorTy, Ext $ WriteVector d rnd' (stripTyLocs el_ty)) <$>
                  go2 marker_added d' rst

              -- Write a pointer to a vector
              ListTy el_ty -> do
                rnd' <- cursorizeExp ddfs fundefs denv tenv senv rnd
                LetE (d',[], CursorTy, Ext $ WriteList d rnd' (stripTyLocs el_ty)) <$>
                  go2 marker_added d' rst

              CursorTy -> do
                rnd' <- cursorizeExp ddfs fundefs denv tenv senv rnd
                LetE (d',[], CursorTy, Ext $ WriteCursor d rnd') <$>
                  go2 marker_added d' rst
              _ -> error $ "Unknown type encounterred while cursorizing DataConE. Type was " ++ show ty

      writetag <- gensym "writetag"
      after_tag <- gensym "after_tag"
      start_tag_alloc <- gensym "start_tag_alloc"
      end_tag_alloc <- gensym "end_tag_alloc"
      start_scalars_alloc <- gensym "start_scalars_alloc"
      dl <$>
        LetE (start_tag_alloc,[],ProdTy [], Ext $ StartTagAllocation sloc) <$>
        LetE (writetag,[], CursorTy, Ext $ WriteTag dcon sloc) <$>
        LetE (end_tag_alloc,[],ProdTy [], Ext $ EndTagAllocation sloc) <$>
        LetE (start_scalars_alloc,[],ProdTy [], Ext $ StartScalarsAllocation sloc) <$>
        LetE (after_tag,[], CursorTy, Ext $ AddCursor sloc (L3.LitE 1)) <$>
          go2 False after_tag (zip args (lookupDataCon ddfs dcon))

    TimeIt e t b -> do
      Di e' <- go tenv senv e
      return $ Di $ TimeIt e' (cursorizeTy t) b

    WithArenaE v e -> do
      Di e' <- go (M.insert v ArenaTy tenv) senv e
      return $ Di $ WithArenaE v e'

    SpawnE{} -> error "cursorizePackedExp: Unbound SpawnE"
    SyncE{}  -> error "cursorizePackedExp: Unbound SyncE"

    Ext ext ->
      case ext of
        -- All locations are transformed into cursors here. Location arithmetic
        -- is expressed in terms of corresponding cursor operations.
        -- See `cursorizeLocExp`
        LetLocE loc rhs bod -> do
          let rhs_either = cursorizeLocExp denv tenv senv loc rhs
              (bnds,tenv') = case M.lookup loc denv of
                               Nothing -> ([],tenv)
                               Just vs -> let extended = M.fromList [ (v,CursorTy) | (v,_,CursorTy,_) <- vs]
                                          in (vs, M.union extended tenv)
          case rhs_either of
            Right (rhs', bnds', tenv'', senv') -> do
              let tenv''' = M.union tenv' tenv''
              case rhs of
                FromEndLE{} ->
                  if isBound loc tenv
                  then go (M.insert loc CursorTy tenv''') senv' bod
                    -- Discharge bindings that were waiting on 'loc'.
                  else onDi (mkLets (bnds' ++ [(loc,[],CursorTy,rhs')] ++ bnds)) <$>
                         go (M.insert loc CursorTy tenv') senv' bod
                -- Discharge bindings that were waiting on 'loc'.
                _ -> onDi (mkLets (bnds' ++ [(loc,[],CursorTy,rhs')] ++ bnds)) <$>
                       go (M.insert loc CursorTy tenv''') senv' bod
            Left denv' -> onDi (mkLets bnds) <$>
                            cursorizePackedExp ddfs fundefs denv' tenv' senv bod

        -- ASSUMPTION: RetE forms are inserted at the tail position of functions,
        -- and we safely just return ends-witnesses & ends of the dilated expressions
        RetE locs v -> do
          v' <- go tenv senv (VarE v)
          case locs of
            []    -> return v'
            [loc] ->  pure $ mkDi (VarE loc) [ fromDi v' ]
            _ -> return $ Di $ L3.MkProdE $ L.foldr (\loc acc -> (VarE loc):acc) [fromDi v'] locs

        LetRegionE r _ _ bod -> do
          onDi (mkLets (regionToBinds False r)) <$> go tenv senv bod

        LetParRegionE r _ _ bod -> do
          onDi (mkLets (regionToBinds True r)) <$> go tenv senv bod

        FromEndE{} -> error $ "cursorizePackedExp: TODO " ++ sdoc ext

        BoundsCheck i bound cur -> return <$> dl <$> Ext $ L3.BoundsCheck i bound cur

        IndirectionE tycon dcon (from,from_reg) (to,to_reg) _ -> do
          dflags <- getDynFlags
          if gopt Opt_DisableGC dflags ||
             (from_reg == "dummy" || to_reg == "dummy") -- HACK!!!
             -- [2022.03.02]: ckoparkar:WTH does this hack enable?
          then go tenv senv (DataConE from dcon [VarE to])
          else do
            start <- gensym "start"
            end <- gensym "end"
            return $ Di $
              (mkLets [("_",[],ProdTy [],Ext (IndirectionBarrier tycon (from,(toEndV from_reg),to,(toEndV to_reg)))),
                       (start, [], CursorTy, VarE from),
                       (end, [], CursorTy, Ext $ AddCursor from (L3.LitE 9))]
                 (MkProdE [VarE start, VarE end]))

        AddFixed{} -> error "cursorizePackedExp: AddFixed not handled."

        GetCilkWorkerNum -> pure $ Di (Ext L3.GetCilkWorkerNum)

        LetAvail vs bod  -> do
          onDi (Ext . L3.LetAvail vs) <$> go tenv senv bod

        AllocateTagHere v tycon -> pure <$> dl <$> Ext $ L3.AllocateTagHere v tycon

        AllocateScalarsHere v -> pure <$> dl <$> Ext $ L3.AllocateScalarsHere v

        SSPush a b c d -> pure <$> dl <$> Ext $ L3.SSPush a b c d
        SSPop a b c -> pure <$> dl <$> Ext $ L3.SSPop a b c

    MapE{}  -> error $ "TODO: cursorizePackedExp MapE"
    FoldE{} -> error $ "TODO: cursorizePackedExp FoldE"

  where go = cursorizePackedExp ddfs fundefs denv
        dl = Di


cursorizeReadPackedFile :: DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> SyncEnv -> Bool -> Var
                        -> Maybe FilePath -> TyCon -> Maybe Var -> Ty2 -> Exp2
                        -> PassM Exp3
cursorizeReadPackedFile ddfs fundefs denv tenv senv isPackedContext v path tyc reg ty2 bod = do
  case reg of
    Nothing -> error $ "cursorizePackedExp: InferLocations did not set the reg for ReadPackedFile."
    Just reg_var ->
      mkLets [ (v, [], CursorTy, PrimAppE (toL3Prim $ ReadPackedFile path tyc reg ty2) [])
             , (reg_var, [], CursorTy, VarE v)
             , (toEndV reg_var, [], CursorTy, Ext$ AddCursor reg_var (Ext $ MMapFileSize v))] <$>
         go (M.insert v CursorTy tenv) bod

  where
    go t e = if isPackedContext
             then fromDi <$> cursorizePackedExp ddfs fundefs denv t senv e
             else cursorizeExp ddfs fundefs denv t senv e

-- We may sometimes encounter a letloc which uses an unbound location.
--
--     letloc loc_b = loc_a + 1
--
-- i.e `loc_a` may not always be bound. If that's the case, don't process `loc_b`
-- now. Instead, add it to the dependency environment.
cursorizeLocExp :: DepEnv -> TyEnv Ty2 -> SyncEnv -> LocVar -> LocExp -> Either DepEnv (Exp3, [Binds Exp3], TyEnv Ty2, SyncEnv)
cursorizeLocExp denv tenv senv lvar locExp =
  case locExp of
    AfterConstantLE i loc ->
      let rhs = Ext $ AddCursor loc (LitE i)
      in if isBound loc tenv
         then Right (rhs, [], tenv, senv)
         else Left$ M.insertWith (++) loc [(lvar,[],CursorTy,rhs)] denv
    -- TODO: handle product types here

{- [2018.03.07]:

Changing it's meaning to just be "after a variable", but not offset from any
particular location. Such an offset requires calculating the size of the variable.
For BigInfinite regions, this is simple:

    size = (endof v) - v

But Infinite regions do not support sizes yet. Re-enable this later.
-}
    AfterVariableLE v loc was_stolen -> do
      let vty = case M.lookup v tenv of
                  Just ty -> ty
                  Nothing -> case M.lookup v senv of
                               Just pending_bnds ->
                                 let tenv' = foldr (\(v1,_,_,ty2,_) env -> M.insert v1 ty2 env) tenv pending_bnds
                                 in case M.lookup v tenv' of
                                      Nothing -> error ("cursorizeLocExp: AfterVariableLE, undound var: " ++ sdoc v)
                                      Just ty -> ty
                               Nothing -> error $ "cursorizeLocExp: Var " ++ sdoc v ++ " not found. "
          bod = case vty of
                  PackedTy{} -> VarE (toEndV v)
                  CursorTy   -> VarE (toEndV v)
                  IntTy -> let sizeVal = LitE (fromJust $ sizeOfTy IntTy)
                               rhs = Ext $ AddCursor loc sizeVal
                           in rhs
                  FloatTy -> let sizeVal = LitE (fromJust $ sizeOfTy FloatTy)
                                 rhs = Ext $ AddCursor loc sizeVal
                             in rhs
                  BoolTy -> let sizeVal = LitE (fromJust $ sizeOfTy BoolTy)
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
                  -- IntTy -> let sizeVar = varAppend "sizeof_" v
                  --              sizeVal = Ext $ SizeOfScalar v
                  --              rhs = Ext $ AddCursor loc (VarE (sizeVar))
                  --          in mkLets [(sizeVar,[], IntTy, sizeVal)] rhs
                  -- FloatTy -> let sizeVar = varAppend "sizeof_" v
                  --                sizeVal = Ext $ SizeOfScalar v
                  --                rhs = Ext $ AddCursor loc (VarE (sizeVar))
                  --            in mkLets [(sizeVar,[], IntTy, sizeVal)] rhs
                  oth -> error $ "cursorizeLocExp: AfterVariable TODO " ++ sdoc oth
      if isBound loc tenv
      then if was_stolen
           then Right (bod, [], tenv, senv)
           -- The continuation was not stolen. It's safe to discharge all
           -- pending bindings of this particular variable.
           else do
              case M.lookup v senv of
                Nothing -> Right (bod, [], tenv, senv)
                Just pending_bnds -> do
                  let tenv' = foldr (\(v1,_,_,ty2,_) env -> M.insert v1 ty2 env) tenv pending_bnds
                      bnds  = map (\(a,b,c,_,e) -> (a,b,c,e)) pending_bnds
                  Right (bod, bnds, tenv', M.delete v senv)
      else Left $ M.insertWith (++) loc [(lvar,[],CursorTy,bod)] denv

    FromEndLE loc -> if isBound loc tenv
                     then Right (VarE loc, [], tenv, senv)
                     else Left$ M.insertWith (++) loc [(lvar,[],CursorTy,VarE loc)] denv
    StartOfLE r   -> case r of
                       GlobR v _ -> Right (VarE v, [], tenv, senv)
                       VarR v    -> Right (VarE v, [], tenv, senv)
                       DynR v _  -> Right (VarE v, [], tenv, senv)
                       -- TODO: docs
                       MMapR _v   -> Left denv


    FreeLE -> Left denv -- AUDIT: should we just throw away this information?

    InRegionLE{}  -> error $ "cursorizeExp: TODO InRegionLE"


-- ASSUMPTIONS:
-- (1) `locs` has [in_regions, out_regions, in_locs, out_locs] for the function.
--     But after Cursorize, the calling convention changes so that input
--     locations appear last. Plus, `arg` would supply those. So we can
--     safely drop them from `locs`.
--
-- (2) We update `arg` so that all packed values in it only have start cursors.
cursorizeAppE :: DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> SyncEnv -> Exp2 -> PassM Exp3
cursorizeAppE ddfs fundefs denv tenv senv ex =
  case ex of
    AppE f locs args -> do
      let fnTy   = case M.lookup f fundefs of
                     Just g -> funTy g
                     Nothing -> error $ "Unknown function: " ++ sdoc f
          in_tys  = arrIns fnTy
          inLocs  = inLocVars fnTy
          numRegs = length (outRegVars fnTy) + length (inRegVars fnTy)
          -- Drop input locations, but keep everything else
          outs    = (L.take numRegs locs) ++  (L.drop numRegs $ L.drop (length inLocs) $ locs)
          argTys  = map (gRecoverType ddfs (Env2 tenv M.empty)) args
      args' <- mapM
                 (\(t,a) -> if hasPacked t
                            then fromDi <$> cursorizePackedExp ddfs fundefs denv tenv senv a
                            else cursorizeExp ddfs fundefs denv tenv senv a)
                 (zip in_tys args)
      let starts = zipWith giveStarts argTys args'
      case locs of
        [] -> return $ AppE f [] starts
        _  -> return $ AppE f [] ([VarE loc | loc <- outs] ++ starts)
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
cursorizeProj :: Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> SyncEnv -> Exp2 -> PassM Exp3
cursorizeProj isPackedContext ddfs fundefs denv tenv senv ex =
  case ex of
    LetE (v,_locs,ty, rhs@ProjE{}) bod | isPackedTy ty -> do
      rhs' <- go tenv rhs
      let ty'  = gRecoverType ddfs (Env2 tenv M.empty) rhs
          ty'' = cursorizeTy ty'
          bnds = if isPackedTy ty'
                 then [ (v       ,[], projValTy ty'' , mkProj 0 rhs')
                      , (toEndV v,[], projEndsTy ty'', mkProj 1 rhs') ]
                 else [(v,[], ty'', rhs')]
          tenv' = if isPackedTy ty'
                  then M.union (M.fromList [(v,ty'), (toEndV v, projEndsTy ty')]) tenv
                  else M.insert v ty' tenv
      bod' <- go tenv' bod
      return $ mkLets bnds bod'

    _ -> error $ "cursorizeProj: Unexpected expression: " ++ sdoc ex

  where
    go t x = if isPackedContext
             then fromDi <$> cursorizePackedExp ddfs fundefs denv t senv x
             else cursorizeExp ddfs fundefs denv t senv x


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
cursorizeProd :: Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> SyncEnv -> Exp2 -> PassM Exp3
cursorizeProd isPackedContext ddfs fundefs denv tenv senv ex =
  case ex of
    LetE (v,_locs,ProdTy tys, rhs@(MkProdE ls)) bod -> do
      es <- forM (zip tys ls) $ \(ty,e) -> do
              case ty of
                  _ | isPackedTy ty -> fromDi <$> cursorizePackedExp ddfs fundefs denv tenv senv e
                  _ | hasPacked ty  -> error $ "cursorizePackedExp: nested tuples" ++ sdoc rhs
                  _ -> cursorizeExp ddfs fundefs denv tenv senv e
      let rhs' = MkProdE es
          ty   = gRecoverType ddfs (Env2 tenv M.empty) rhs
          ty'  = cursorizeTy ty
          tenv' = M.insert v ty tenv
      bod' <- go tenv' bod
      return $ mkLets [(v,[], ty', rhs')] bod'

    _ -> error $ "cursorizeProj: Unexpected expression: " ++ sdoc ex

  where
    go t x = if isPackedContext
             then fromDi <$> cursorizePackedExp ddfs fundefs denv t senv x
             else cursorizeExp ddfs fundefs denv t senv x


{-

Spawn and sync
~~~~~~~~~~~~~~

This is almost identical to a cursorizeLet case below. Except we bind fewer things
and add fewer things to the type environemnt because we have to wait until the
join point.

-}
cursorizeSpawn :: Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> SyncEnv -> Exp2 -> PassM Exp3
cursorizeSpawn isPackedContext ddfs fundefs denv tenv senv ex = do
  case ex of
    LetE (v, locs, ty, (SpawnE fn applocs args)) bod

      | isPackedTy ty -> do
          rhs' <- fromDi <$> cursorizePackedExp ddfs fundefs denv tenv senv (AppE fn applocs args)
          let rhs'' = case rhs' of
                        AppE fn' applocs' args' -> SpawnE fn' applocs' args'
                        _ -> error "cursorizeSpawn"
          fresh <- gensym "tup_packed"
          let ty' = case locs of
                      [] -> cursorizeTy ty
                      xs -> ProdTy ([CursorTy | _ <- xs] ++ [cursorizeTy ty])
              tenv' = M.union (M.fromList [(fresh, ty')]) tenv
                      -- L.foldr (\(a,b) acc -> M.insert a b acc) tenv $
                      --   [(v, ty),(fresh, ty'),(toEndV v, projTy 1 ty')] ++ [(loc,CursorTy) | loc <- locs]
              -- TyEnv Ty2 and L3 expresssions are tagged with different types
              ty''  = curDict $ stripTyLocs ty'
              fresh_rhs = VarE fresh
              (bnds, pending_bnds) =
                      case locs of
                        []    -> ([ (fresh   , [], ty''          , rhs'' ) ],
                                  [ (v       , [], projTy 0 ty'', ty,           mkProj 0 fresh_rhs)
                                  , (toEndV v, [], projTy 1 ty'', projTy 1 ty', mkProj 1 fresh_rhs)])
                        _ -> let nLocs = length locs
                                 locBnds = [(loc  ,[], CursorTy, CursorTy, mkProj n fresh_rhs)
                                           | (loc,n) <- zip locs [0..]]
                                 bnds' = [(fresh ,[], ty'', rhs'') ]
                                 pending_bnds' = [(v       ,[], projTy 0 $ projTy nLocs ty'', ty,                          mkProj 0 $ mkProj nLocs fresh_rhs)
                                                 ,(toEndV v,[], projTy 1 $ projTy nLocs ty'', projTy 0 $ projTy nLocs ty', mkProj 1 $ mkProj nLocs fresh_rhs)]
                                                 ++ locBnds
                             in (bnds', pending_bnds')
          case M.lookup (toEndV v) denv of
            Just xs -> error $ "cursorizeSpawn todo: " ++ sdoc xs
            Nothing -> return ()
          let senv' = M.insert v pending_bnds senv
          bod'  <- go tenv' senv' bod
          let bod'' = updateAvailVars [v] [fresh] bod'
          return $ mkLets bnds bod''

      | hasPacked ty -> do
          rhs' <- fromDi <$> cursorizePackedExp ddfs fundefs denv tenv senv (AppE fn applocs args)
          let rhs'' = case rhs' of
                        AppE fn' applocs' args' -> SpawnE fn' applocs' args'
                        _ -> error $ "cursorizeSpawn: this should've been an AppE. Got" ++ sdoc rhs'
          fresh <- gensym "tup_haspacked"
          let ty' = case locs of
                      [] -> cursorizeTy ty
                      xs -> ProdTy ([CursorTy | _ <- xs] ++ [cursorizeTy ty])
              ty''  = stripTyLocs ty'
              tenv' = M.insert v ty tenv
          case locs of
            [] -> LetE (v,[], ty'', rhs'') <$>
                    go tenv' senv bod
            _  -> do
              let (bnds, pending_bnds) =
                    ([(fresh, [], ty'', rhs'')],
                     [(loc,[],CursorTy, CursorTy, ProjE n (VarE fresh)) | (loc,n) <- (zip locs [0..])] ++
                     [(v,[], projTy (length locs) ty'', ty, ProjE (length locs) (VarE fresh))])
                  senv' = M.insert v pending_bnds senv
              mkLets bnds <$> go tenv' senv' bod

      | otherwise -> do
          rhs' <- cursorizeExp ddfs fundefs denv tenv senv (AppE fn applocs args)
          let rhs'' = case rhs' of
                        AppE fn' applocs' args' -> SpawnE fn' applocs' args'
                        _ -> error "cursorizeSpawn"
          case locs of
            [] -> LetE (v,[],curDict $ stripTyLocs ty, rhs'') <$>
                    go (M.insert v ty tenv) senv bod
            [loc] -> do
              fresh <- gensym "par_tup_scalar"
              let ty' :: Ty2
                  ty'  = ProdTy ([CursorTy | _ <- locs] ++ [cursorizeTy ty])
                  tenv' = M.union (M.fromList [(fresh, ty')]) tenv
                  ty'' :: Ty3
                  ty'' = stripTyLocs ty'
                  rhs''' = Di (VarE fresh)
                  pending_bnds = [ (loc   ,[] , projTy 0 ty'', projTy 0 ty' , projVal rhs''')
                                 , (v     ,[] , projTy 1 ty'', projTy 0 ty' , projEnds rhs''')]
                  senv' = M.insert v pending_bnds senv
              bod' <- go tenv' senv' bod
              return $ mkLets [(fresh,[] , ty'', rhs'')] bod'

            _ -> error "TODO: cursorizeSpawn"

    _ -> error "cursorizeSpawn: Unbound SpawnE"

  where go t s x = if isPackedContext
                   then fromDi <$> cursorizePackedExp ddfs fundefs denv t s x
                   else cursorizeExp ddfs fundefs denv t s x

cursorizeSync :: Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> SyncEnv -> Exp2 -> PassM Exp3
cursorizeSync isPackedContext ddfs fundefs denv tenv senv ex = do
  case ex of
    LetE (v, _locs, ty, SyncE) bod -> do
      let pending_bnds = concat (M.elems senv)
          tenv' = foldr (\(v1,_,_,ty2,_) env -> M.insert v1 ty2 env) tenv pending_bnds
          -- Discharge bindings that depending on the join point.
          bnds  = map (\(a,b,c,_,e) -> (a,b,c,e)) pending_bnds
          bnds' = (v,[],stripTyLocs ty, SyncE) : bnds
      bod' <- go tenv' bod
      return $ mkLets bnds' bod'
    _ -> error "cursorizeSpawn: Unbound SyncE"
  where go t x = if isPackedContext
                 then fromDi <$> cursorizePackedExp ddfs fundefs denv t M.empty x
                 else cursorizeExp ddfs fundefs denv t M.empty x


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
cursorizeLet :: Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> SyncEnv
             -> (Var, [Var], Ty2, Exp2) -> Exp2 -> PassM Exp3
cursorizeLet isPackedContext ddfs fundefs denv tenv senv (v,locs,ty,rhs) bod
    | isPackedTy ty = do
        rhs' <- fromDi <$> cursorizePackedExp ddfs fundefs denv tenv senv rhs
        fresh <- gensym "tup_packed"
        let ty' = case locs of
                    [] -> cursorizeTy ty
                    xs -> ProdTy ([CursorTy | _ <- xs] ++ [cursorizeTy ty])

            tenv' = L.foldr (\(a,b) acc -> M.insert a b acc) tenv $
                      [(v, ty),(fresh, ty'),(toEndV v, projTy 1 ty')] ++ [(loc,CursorTy) | loc <- locs]

            -- TyEnv Ty2 and L3 expresssions are tagged with different types
            ty''  = curDict $ stripTyLocs ty'
            rhs'' = VarE fresh

            bnds = case locs of
                      []    -> [ (fresh   , [], ty''          , rhs' )
                               , (v       , [], projTy 0 ty'' , mkProj 0 rhs'')
                               , (toEndV v, [], projTy 1 ty'' , mkProj 1 rhs'')]

                      _ -> let nLocs = length locs
                               locBnds = [(loc  ,[], CursorTy, mkProj n rhs'')
                                         | (loc,n) <- zip locs [0..]]
                               bnds' = [(fresh   ,[], ty''                         , rhs')
                                       ,(v       ,[], projTy 0 $ projTy nLocs ty'' , mkProj 0 $ mkProj nLocs rhs'')
                                       ,(toEndV v,[], projTy 1 $ projTy nLocs ty'' , mkProj 1 $ mkProj nLocs rhs'')]
                           in bnds' ++ locBnds
        case M.lookup (toEndV v) denv of
          Just xs -> error $ "todo: " ++ sdoc xs
          Nothing -> return ()
        bod' <- go tenv' bod
        return $ mkLets bnds bod'

    | hasPacked ty = do
        rhs' <- fromDi <$> cursorizePackedExp ddfs fundefs denv tenv senv rhs
        fresh <- gensym "tup_haspacked"
        let ty' = case locs of
                    [] -> cursorizeTy ty
                    xs -> ProdTy ([CursorTy | _ <- xs] ++ [cursorizeTy ty])
            ty''  = stripTyLocs ty'
            tenv' = M.union (M.insert v ty tenv) (M.fromList [(loc,CursorTy) | loc <- locs])
        case locs of
          [] -> LetE (v,[], ty'', rhs') <$>
                  go tenv' bod
          _  -> do
            let tenv'' =  M.union tenv' $
                          M.fromList [(loc,CursorTy) | loc <- locs]

                bnds  = [(fresh, [], ty'', rhs')] ++
                        [(loc,[],CursorTy, ProjE n (VarE fresh)) | (loc,n) <- (zip locs [0..])]
                        ++ [(v,[], projTy (length locs) ty'', ProjE (length locs) (VarE fresh))]
            mkLets bnds <$> go tenv'' bod

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
        rhs' <- cursorizeExp ddfs fundefs denv tenv senv rhs
        case locs of
            [] -> LetE (v,[],curDict $ stripTyLocs ty, rhs') <$>
                    go (M.insert v ty tenv) bod
            _ -> do
              fresh <- gensym "tup_scalar"
              let rhs'' = VarE fresh
                  ty'  = ProdTy ([CursorTy | _ <- locs] ++ [cursorizeTy ty])
                  -- We cannot resuse ty' here because TyEnv Ty2 and expresssions are
                  -- tagged with different
                  ty'' = stripTyLocs ty'
                  tenv' =  M.union (M.insert v ty tenv) $
                           M.fromList [(loc,CursorTy) | loc <- locs]
                  bnds  = [ (fresh, [] , ty''          , rhs') ] ++
                          [ (loc,[],CursorTy, ProjE n rhs'') | (loc,n) <- (zip locs [0..]) ] ++
                          [ (v,[], projTy (length locs) ty'', ProjE (length locs) rhs'') ]
              bod' <- go tenv' bod
              return $ mkLets bnds bod'

  where go t x = if isPackedContext
                 then fromDi <$> cursorizePackedExp ddfs fundefs denv t senv x
                 else cursorizeExp ddfs fundefs denv t senv x

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
unpackDataCon :: DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> SyncEnv -> Bool -> Var
              -> (DataCon, [(Var, Var)], Exp2) -> PassM (DataCon, [t], Exp3)
unpackDataCon ddfs fundefs denv1 tenv1 senv isPacked scrtCur (dcon,vlocs1,rhs) = do
  field_cur <- gensym "field_cur"

  (dcon, [],)
    -- Advance the cursor by 1 byte so that it points to the first field
    <$> mkLets [(field_cur,[],CursorTy, Ext $ AddCursor scrtCur (LitE 1))]
    <$> (if isAbsRANDataCon dcon
         then unpackWithAbsRAN field_cur
         else if isRelRANDataCon dcon
         then unpackWithRelRAN field_cur
         else unpackRegularDataCon field_cur)

  where
    tys1 = lookupDataCon ddfs dcon
    processRhs denv env = if isPacked
                          then fromDi <$> cursorizePackedExp ddfs fundefs denv env senv rhs
                          else cursorizeExp ddfs fundefs denv env senv rhs

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
    unpackRegularDataCon :: Var -> PassM Exp3
    unpackRegularDataCon field_cur = go field_cur vlocs1 tys1 True denv1 (M.insert field_cur CursorTy tenv1)
      where
        go :: Var -> [(Var, LocVar)] -> [Ty2] -> Bool -> DepEnv -> TyEnv Ty2 -> PassM Exp3
        go cur vlocs tys canBind denv tenv =
          case (vlocs, tys) of
            ([],[]) -> processRhs denv tenv
            ((v,loc):rst_vlocs, ty:rst_tys) ->
              case ty of
                -- Int, Float, Sym, or Bool
                _ | isScalarTy ty -> do
                  (tenv', binds) <- scalarBinds ty v loc tenv
                  if canBind
                  then do
                    -- If the location exists in the environment, it indicates that the
                    -- corresponding variable was also bound and we shouldn't create duplicate
                    -- bindings (checked in the LetLocE cases).
                    let binds' = (loc,[],CursorTy, VarE cur):binds
                        tenv'' = M.insert loc CursorTy tenv'
                    bod <- go (toEndV v) rst_vlocs rst_tys canBind denv tenv''
                    return $ mkLets binds' bod
                  else do
                    -- Cannot read this int. Instead, we add it to DepEnv.
                    let denv' = M.insertWith (++) loc binds denv
                    go (toEndV v) rst_vlocs rst_tys canBind denv' tenv'

                -- An indirection or redirection pointer.
                -- ASSUMPTION: We can always bind it, since it occurs immediately after the tag.
                CursorTy -> do
                  tmp <- gensym "readcursor_indir"
                  let tenv' = M.union (M.fromList [(tmp     , ProdTy [CursorTy, CursorTy]),
                                                   (loc     , CursorTy),
                                                   (v       , CursorTy),
                                                   (toEndV v, CursorTy)])
                              tenv
                      read_cursor = if isIndirectionTag dcon || isRedirectionTag dcon
                                    then Ext (ReadTaggedCursor cur)
                                    else error $ "unpackRegularDataCon: cursorty without indirection/redirection."
                      binds = [(tmp     , [], ProdTy [CursorTy, CursorTy], read_cursor),
                               (loc     , [], CursorTy, VarE cur),
                               (v       , [], CursorTy, ProjE 0 (VarE tmp)),
                               (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                  bod <- go (toEndV v) rst_vlocs rst_tys canBind denv tenv'
                  return $ mkLets binds bod


                VectorTy el_ty -> do
                  tmp <- gensym "read_vec_tuple"
                  let tenv' = M.union (M.fromList [(tmp     , ProdTy [VectorTy el_ty, CursorTy]),
                                                   (v       , VectorTy el_ty),
                                                   (toEndV v, CursorTy)])
                              tenv
                      ty'   = stripTyLocs ty
                      binds = [(tmp     , [], ProdTy [ty', CursorTy], Ext $ ReadVector loc (stripTyLocs el_ty)),
                               (v       , [], ty'     , ProjE 0 (VarE tmp)),
                               (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                  if canBind
                  then do
                    -- If the location exists in the environment, it indicates that the
                    -- corresponding variable was also bound and we shouldn't create duplicate
                    -- bindings (checked in the LetLocE cases).
                    let binds' = (loc,[],CursorTy, VarE cur):binds
                        tenv'' = M.insert loc CursorTy tenv'
                    bod <- go (toEndV v) rst_vlocs rst_tys canBind denv tenv''
                    return $ mkLets binds' bod
                  else do
                    -- Cannot read this int. Instead, we add it to DepEnv.
                    let denv' = M.insertWith (++) loc binds denv
                    go (toEndV v) rst_vlocs rst_tys canBind denv' tenv'


                ListTy el_ty -> do
                  tmp <- gensym "read_list_tuple"
                  let tenv' = M.union (M.fromList [(tmp     , ProdTy [VectorTy el_ty, CursorTy]),
                                                   (v       , ListTy el_ty),
                                                   (toEndV v, CursorTy)])
                              tenv
                      ty'   = stripTyLocs ty
                      binds = [(tmp     , [], ProdTy [ty', CursorTy], Ext $ ReadList loc (stripTyLocs el_ty)),
                               (v       , [], ty'     , ProjE 0 (VarE tmp)),
                               (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                  if canBind
                  then do
                    -- If the location exists in the environment, it indicates that the
                    -- corresponding variable was also bound and we shouldn't create duplicate
                    -- bindings (checked in the LetLocE cases).
                    let binds' = (loc,[],CursorTy, VarE cur):binds
                        tenv'' = M.insert loc CursorTy tenv'
                    bod <- go (toEndV v) rst_vlocs rst_tys canBind denv tenv''
                    return $ mkLets binds' bod
                  else do
                    -- Cannot read this int. Instead, we add it to DepEnv.
                    let denv' = M.insertWith (++) loc binds denv
                    go (toEndV v) rst_vlocs rst_tys canBind denv' tenv'

                PackedTy{} -> do
                  let tenv' = M.insert v CursorTy tenv
                  if canBind
                  then do
                    let tenv'' = M.insert loc CursorTy tenv'
                    -- Flip canBind to indicate that the subsequent fields
                    -- should be added to the dependency environment.
                    bod <- go (toEndV v) rst_vlocs rst_tys False denv tenv''
                    return $ mkLets [(loc, [], CursorTy, VarE cur)
                                    ,(v  , [], CursorTy, VarE loc)]
                             bod
                  else do
                    -- Cannot read this. Instead, we add it to DepEnv.
                    let denv' = M.insertWith (++) loc [(v,[],CursorTy,VarE loc)] denv
                    go (toEndV v) rst_vlocs rst_tys False denv' tenv'

                _ -> error $ "unpackRegularDataCon: Unexpected field " ++ sdoc (v,loc) ++ ":" ++ sdoc ty

            _ -> error $ "unpackRegularDataCon: Unexpected numnber of varible, type pairs: " ++ show (vlocs,tys)

    -- We have access to all fields in this constructor, and can create
    -- bindings for everything. We begin by unpacking the random access nodes.
    unpackWithAbsRAN :: Var -> PassM Exp3
    unpackWithAbsRAN field_cur =
        -- A map from a variable to a tuple containing it's location and
        -- the RAN field it depends on. Consider this constructor:
        --
        --     (Node^ [(ran_y3, loc_ran_y3), (n1, loc_n1) , (x2 , loc_x2), (y3 , loc_y3)] ...),
        --
        -- it will be the map:
        --
        --     (y3 -> (loc_y3, ran_y3))
        let ran_mp =
              case numRANsDataCon ddfs (fromRANDataCon dcon) of
                0 -> M.empty
                n -> let -- Random access nodes occur immediately after the tag
                         ind_vars = L.map fst $ L.take n vlocs1
                         -- Everything else is a regular consturctor field,
                         -- which depends on some random access node
                         data_fields = reverse $ L.take n (reverse vlocs1)
                         (vars, var_locs) = unzip data_fields
                     in M.fromList $ zip vars (zip var_locs ind_vars)
        in go field_cur vlocs1 tys1 ran_mp denv1 (M.insert field_cur CursorTy tenv1)
      where
        go :: Var -> [(Var, LocVar)] -> [Ty2] -> M.Map Var (Var,Var) -> DepEnv -> TyEnv Ty2 -> PassM Exp3
        go cur vlocs tys indirections_env denv tenv = do
          case (vlocs, tys) of
            ([], []) -> processRhs denv tenv
            ((v,loc):rst_vlocs, ty:rst_tys) ->
              case ty of
                -- The random access node
                -- ASSUMPTION: We can always bind it, since it occurs immediately after the tag.
                CursorTy -> do
                  tmp <- gensym "readcursor_tuple"
                  let tenv' = M.union (M.fromList [(tmp     , ProdTy [CursorTy, CursorTy]),
                                                   (loc     , CursorTy),
                                                   (v       , CursorTy),
                                                   (toEndV v, CursorTy)])
                              tenv

                      binds = [(tmp     , [], ProdTy [CursorTy, CursorTy], Ext $ ReadCursor cur),
                               (loc     , [], CursorTy, VarE cur),
                               (v       , [], CursorTy, ProjE 0 (VarE tmp)),
                               (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv'
                  return $ mkLets binds bod

                -- Int, Sym, or Bool
                _ | isScalarTy ty -> do
                  (tenv', binds) <- scalarBinds ty v loc tenv
                  let loc_bind = case M.lookup v indirections_env of
                                   Nothing ->
                                     (loc,[],CursorTy, VarE cur)
                                   -- Read this using a random access node
                                   Just (_var_loc, ind_var) ->
                                     (loc,[],CursorTy, VarE ind_var)
                      binds' = loc_bind:binds
                      tenv'' = M.insert loc CursorTy tenv'
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv''
                  return $ mkLets binds' bod

                VectorTy el_ty -> do
                  tmp <- gensym "read_vec_tuple"
                  let tenv' = M.union (M.fromList [(tmp     , ProdTy [VectorTy el_ty, CursorTy]),
                                                   (v       , VectorTy el_ty),
                                                   (toEndV v, CursorTy)])
                              tenv
                      ty'   = stripTyLocs ty
                      binds = [(tmp     , [], ProdTy [ty', CursorTy], Ext $ ReadVector loc (stripTyLocs el_ty)),
                               (v       , [], ty'     , ProjE 0 (VarE tmp)),
                               (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                      loc_bind = case M.lookup v indirections_env of
                                   Nothing ->
                                     (loc, [], CursorTy, VarE cur)
                                   Just (_var_loc, ind_var) ->
                                     (loc, [], CursorTy, VarE ind_var)
                      binds' = loc_bind : binds
                      tenv'' = M.insert loc CursorTy tenv'
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv''
                  return $ mkLets binds' bod

                ListTy el_ty -> do
                  tmp <- gensym "read_list_tuple"
                  let tenv' = M.union (M.fromList [(tmp     , ProdTy [VectorTy el_ty, CursorTy]),
                                                   (v       , ListTy el_ty),
                                                   (toEndV v, CursorTy)])
                              tenv
                      ty'   = stripTyLocs ty
                      binds = [(tmp     , [], ProdTy [ty', CursorTy], Ext $ ReadList loc (stripTyLocs el_ty)),
                               (v       , [], ty'     , ProjE 0 (VarE tmp)),
                               (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
                      loc_bind = case M.lookup v indirections_env of
                                   Nothing ->
                                     (loc, [], CursorTy, VarE cur)
                                   Just (_var_loc, ind_var) ->
                                     (loc, [], CursorTy, VarE ind_var)
                      binds' = loc_bind : binds
                      tenv'' = M.insert loc CursorTy tenv'
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv''
                  return $ mkLets binds' bod

                PackedTy{} -> do
                  let tenv' = M.union (M.fromList [ (loc, CursorTy)
                                                  , (v,   CursorTy) ])
                              tenv
                      loc_bind = case M.lookup v indirections_env of
                                   -- This is the first packed value. We can unpack this.
                                   Nothing ->
                                     (loc, [], CursorTy, VarE cur)
                                   -- We need to access this using a random access node
                                   Just (_var_loc, ind_var) ->
                                     (loc, [], CursorTy, VarE ind_var)
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv'
                  return $ mkLets [ loc_bind, (v, [], CursorTy, VarE loc) ] bod

                _ -> error $ "unpackWitnAbsRAN: Unexpected field " ++ sdoc (v,loc) ++ ":" ++ sdoc ty

            _ -> error $ "unpackWitnAbsRAN: Unexpected numnber of varible, type pairs: " ++ show (vlocs,tys)

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
              case numRANsDataCon ddfs (fromRANDataCon dcon) of
                0 -> M.empty
                n -> let -- Random access nodes occur immediately after the tag
                         inds = L.take n $ L.drop 1 vlocs1
                         -- Everything else is a regular consturctor field,
                         -- which depends on some random access node
                         data_fields = reverse $ L.take n (reverse vlocs1)
                         (vars, var_locs) = unzip data_fields
                     in M.fromList $ zip vars (zip var_locs inds)
        in go field_cur vlocs1 tys1 ran_mp denv1 (M.insert field_cur CursorTy tenv1)
      where
        go :: Var -> [(Var, LocVar)] -> [Ty2] -> M.Map Var (Var,(Var,Var)) -> DepEnv -> TyEnv Ty2 -> PassM Exp3
        go cur vlocs tys indirections_env denv tenv = do
          case (vlocs, tys) of
            ([], []) -> processRhs denv tenv
            ((v,loc):rst_vlocs, ty:rst_tys) ->
              case ty of
                -- Int, Sym, or Bool
                _ | isScalarTy ty -> do
                  (tenv', binds) <- scalarBinds ty v loc tenv
                  let loc_bind = case M.lookup v indirections_env of
                                   -- This appears before the first packed field. Unpack it
                                   -- in the usual way.
                                   Nothing ->
                                     (loc,[],CursorTy, VarE cur)
                                   -- We need to read this using a random access node
                                   Just (_var_loc, (ind_var, ind_loc)) ->
                                     (loc,[],CursorTy, Ext $ AddCursor ind_loc (VarE ind_var))
                      binds' = loc_bind:binds
                      tenv'' = M.insert loc CursorTy tenv'
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv''
                  return $ mkLets binds' bod

                PackedTy{} -> do
                  tmp_loc <- gensym "loc"
                  let tenv' = M.union (M.fromList [ (loc, CursorTy)
                                                  , (v,   CursorTy) ])
                              tenv
                      loc_binds = case M.lookup v indirections_env of
                                    -- This is the first packed value. We can unpack this.
                                    Nothing ->
                                      [(loc, [], CursorTy, VarE cur)]
                                    -- We need to access this using a random access node
                                    Just (_var_loc, (ind_var, ind_loc)) ->
                                      [ (tmp_loc,[],CursorTy, Ext $ AddCursor ind_loc (VarE ind_var))
                                      , (loc,[],CursorTy, Ext $ AddCursor tmp_loc (LitE 8)) ]
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv'
                  return $ mkLets  (loc_binds ++ [(v, [], CursorTy, VarE loc)]) bod

                _ -> error $ "unpackWithRelRAN: Unexpected field " ++ sdoc (v,loc) ++ ":" ++ sdoc ty

            _ -> error $ "unpackWithRelRAN: Unexpected numnber of varible, type pairs: " ++ show (vlocs,tys)

    -- Generate bindings for unpacking int fields. A convenient
    scalarBinds :: Ty2 -> Var -> LocVar -> TyEnv Ty2 -> PassM (TyEnv Ty2, [(Var, [()], Ty3, Exp3)])
    scalarBinds ty v loc tenv = do
      tmp <- gensym "read_scalar_tuple"
      -- Note that the location is not added to the type environment here.
      -- The caller of this fn will do that later, depending on whether we're
      -- binding the location now or later via DepEnv.
      let s     = mkScalar ty
          tenv' = M.union (M.fromList [(tmp     , ProdTy [ty, CursorTy]),
                                       (v       , ty),
                                       (toEndV v, CursorTy)])
                  tenv

          ty'   = stripTyLocs ty

          binds = [(tmp     , [], ProdTy [ty', CursorTy], Ext $ ReadScalar s loc),
                   (v       , [], ty'     , ProjE 0 (VarE tmp)),
                   (toEndV v, [], CursorTy, ProjE 1 (VarE tmp))]
      return (tenv', binds)

giveStarts :: Ty2 -> Exp3 -> Exp3
giveStarts ty e =
  case ty of
    PackedTy{} -> mkProj 0 e
    -- NOTE : mkProj . MkProdE == id
    ProdTy tys -> MkProdE $ zipWith (\ ty' n -> giveStarts ty' (mkProj n e)) tys [0..]
    _ -> e


projValTy :: (Out a) => UrTy a -> UrTy a
projValTy = projTy 0

projEndsTy :: (Out a) => UrTy a -> UrTy a
projEndsTy = projTy 1


-- | Bindings for a letregion
regionToBinds :: Bool -> Region -> [(Var, [()], Ty3, Exp3)]
regionToBinds for_parallel_allocs r =
  case r of
    VarR{} -> error $ "Unexpected VarR in Cursorize." ++ sdoc r
    GlobR v mul -> if for_parallel_allocs
                   then [ (v       , [], CursorTy, Ext$ NewParBuffer mul)
                        , (toEndV v, [], CursorTy, Ext$ EndOfBuffer mul)]
                   else [ (v       , [], CursorTy, Ext$ NewBuffer mul)
                        , (toEndV v, [], CursorTy, Ext$ EndOfBuffer mul)]
    DynR v mul  -> if for_parallel_allocs
                   then [ (v       , [], CursorTy, Ext$ ScopedParBuffer mul)
                        , (toEndV v, [], CursorTy, Ext$ EndOfBuffer mul)]
                   else [ (v       , [], CursorTy, Ext$ ScopedBuffer mul)
                        , (toEndV v, [], CursorTy, Ext$ EndOfBuffer mul)]
    -- TODO: docs
    MMapR _v    -> []

isBound :: LocVar -> TyEnv Ty2 -> Bool
isBound = M.member

-- ================================================================================
--                         Dilation Conventions
-- ================================================================================
-- Everything to do with dilation.  It should be possible to change
-- the dilated format by changing only this section.


-- | If an expression `e` returns type `T`, then a dilated version of
-- `e` returns a tuple (T,Cursors), where cursors contains a flat
-- record of end-cursors corresponding exactly to all the components
-- of T which are PackedTy.
--
newtype DiExp ex = Di ex
  deriving (Generic, Show, Read, Eq, Ord)
--type DiExp = Exp

instance (Out ex) => Out (DiExp ex)

onDi :: (ex -> ex) -> DiExp ex -> DiExp ex
onDi f (Di x) = Di (f x)

fromDi :: DiExp ex -> ex
fromDi (Di x) = x


-- | Project the cursor package from a dilated expression, contains pointers
-- to all the ENDs.
projEnds :: DiExp Exp3 -> Exp3
projEnds (Di e) = mkProj 1 e

-- | Project the original value from a dilated expression.
projVal :: DiExp Exp3 -> Exp3
projVal (Di e) = mkProj 0 e

-- | Constructor that combines a regular expression with a list of
-- corresponding end cursors.
mkDi :: Exp3 -> [Exp3] -> DiExp Exp3
mkDi x []  = Di $ MkProdE [x,MkProdE []]
mkDi x [o] = Di $ MkProdE [x, o]
mkDi x ls  = Di $ MkProdE [x, MkProdE ls]

curDict :: UrTy a -> UrTy a
curDict (SymDictTy ar _ty) = SymDictTy ar CursorTy
curDict ty = ty
