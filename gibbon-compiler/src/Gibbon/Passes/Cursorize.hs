module Gibbon.Passes.Cursorize
  (cursorize) where

import           Control.Monad (forM)
import           Data.Loc
import           Data.List as L
import qualified Data.Map as M
import           Text.PrettyPrint.GenericPretty

import           Gibbon.DynFlags
import           Gibbon.Common
import           Gibbon.L2.Syntax
import           Gibbon.L3.Syntax hiding ( BoundsCheck )
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
type DepEnv = M.Map LocVar [(Var,[()],Ty3,L Exp3)]

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
                         fromDi <$> cursorizePackedExp ddefs fundefs M.empty M.empty e
                  else Just . (,stripTyLocs ty) <$>
                         cursorizeExp ddefs fundefs M.empty M.empty e
  pure (Prog ddefs' fundefs' mainExp')

-- |
cursorizeFunDef :: DDefs Ty2 -> FunDefs2 -> FunDef2 -> PassM FunDef3
cursorizeFunDef ddefs fundefs FunDef{funName,funTy,funArgs,funBody} = do
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
                           let projs = concatMap (uncurry mkInProjs) (zip (map (l . VarE) funArgs) in_tys)
                               bnds  = [(loc,[],CursorTy,proj) | (loc,proj) <- zip inLocs projs]
                           in mkLets bnds

      initTyEnv = M.fromList $ (map (\(a,b) -> (a,cursorizeInTy b)) $ zip funArgs in_tys) ++
                               [(a,CursorTy) | (LRM a _ _) <- locVars funTy]

      funargs = regBinds ++ outCurBinds ++ funArgs

  bod <- if hasPacked out_ty
         then fromDi <$> cursorizePackedExp ddefs fundefs M.empty initTyEnv funBody
         else cursorizeExp ddefs fundefs M.empty initTyEnv funBody
  let bod' = inCurBinds bod
      fn = FunDef funName funargs funTy' bod'
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
        SymTy     -> SymTy
        BoolTy    -> BoolTy
        ProdTy ls -> ProdTy $ L.map cursorizeInTy ls
        SymDictTy ar _ty -> SymDictTy ar CursorTy -- $ cursorizeInTy ty'
        PackedTy{}    -> CursorTy
        ListTy ty'    -> ListTy $ cursorizeInTy ty'
        PtrTy -> PtrTy
        CursorTy -> CursorTy
        ArenaTy -> ArenaTy

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
    mkInProjs :: L Exp3 -> Ty2 -> [L Exp3]
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
cursorizeExp :: DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> L Exp2 -> PassM (L Exp3)
cursorizeExp ddfs fundefs denv tenv (L p ex) = L p <$>
  case ex of
    VarE v    -> return $ VarE v
    LitE n    -> return $ LitE n
    LitSymE n -> return $ LitSymE n

    AppE{} -> cursorizeAppE ddfs fundefs denv tenv (L p ex)

    PrimAppE PEndOf [arg] -> do
      let (L _ (VarE v)) = arg
      return $ VarE (toEndV v)

    PrimAppE pr args -> PrimAppE (toL3Prim pr) <$> mapM go args

    LetE (v,_locs, _ty, L _ (PrimAppE (ReadPackedFile path tyc reg ty2) [])) bod ->
      unLoc <$> cursorizeReadPackedFile ddfs fundefs denv tenv True v path tyc reg ty2 bod

    LetE (_v,_locs,_ty, (L _ (MkProdE _ls))) _bod ->
      cursorizeProd False ddfs fundefs denv tenv ex

    LetE (_v,_locs, ty, (L _ ProjE{})) _bod | isPackedTy ty ->
       cursorizeProj False ddfs fundefs denv tenv ex

    LetE (_v,_locs,_ty, (L _ (ParE{}))) _bod ->
      cursorizePar False ddfs fundefs denv tenv ex

    LetE bnd bod -> cursorizeLet False ddfs fundefs denv tenv bnd bod

    IfE a b c  -> IfE <$> go a <*> go b <*> go c

    MkProdE ls -> MkProdE <$> mapM go ls

    ProjE i e  -> ProjE i <$> go e

    -- Eg. leftmost
    CaseE scrt brs -> do
      -- ASSUMPTION: scrt is flat
      let (L _ (VarE  v)) = scrt
      CaseE (l$ VarE $ v) <$>
        mapM (unpackDataCon ddfs fundefs denv tenv False v) brs

    DataConE _ _ _ -> error $ "cursorizeExp: Should not have encountered DataConE if type is not packed: "++ndoc ex

    TimeIt e ty b -> TimeIt <$> go e <*> pure (stripTyLocs ty) <*> pure b

    ParE a b -> ParE <$> go a <*> go b

    WithArenaE v e -> do
      e' <- cursorizeExp ddfs fundefs denv (M.insert v ArenaTy tenv) e
      return $ WithArenaE v e'

    -- Eg. leftmost
    Ext ext ->
      case ext of
        RetE locs v ->
          case locs of
              [] -> return (VarE v)
              _  -> return $ MkProdE $ [l$ VarE loc | loc <- locs] ++ [l$ VarE v]

        -- All locations are transformed into cursors here. Location arithmetic
        -- is expressed in terms of corresponding cursor operations.
        -- See `cursorizeLocExp`
        LetLocE loc rhs bod -> do
          let rhs_either = cursorizeLocExp denv tenv loc rhs
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
            Right rhs' ->
              case M.lookup loc tenv of
                Nothing ->  unLoc . mkLets ((loc,[],CursorTy,rhs') : bnds) <$>
                              cursorizeExp ddfs fundefs denv (M.insert loc CursorTy tenv') bod
                Just _  -> unLoc <$> cursorizeExp ddfs fundefs denv (M.insert loc CursorTy tenv') bod
            Left denv' -> unLoc <$> cursorizeExp ddfs fundefs denv' tenv' bod

        -- Exactly same as cursorizePackedExp
        LetRegionE reg bod -> do
          unLoc <$> mkLets (regionToBinds reg) <$> go bod

        BoundsCheck i bound cur -> return $ Ext $ L3.BoundsCheck i bound cur

        FromEndE{} -> error $ "cursorizeExp: TODO FromEndE" ++ sdoc ext

        IndirectionE{} -> error $ "cursorizeExp: Unexpected IndirectionE"

    MapE{} -> error $ "TODO: cursorizeExp MapE"
    FoldE{} -> error $ "TODO: cursorizeExp FoldE"

  where
    go = cursorizeExp ddfs fundefs denv tenv


-- Cursorize expressions producing `Packed` values
cursorizePackedExp :: DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> L Exp2
                   -> PassM (DiExp (L Exp3))
cursorizePackedExp ddfs fundefs denv tenv (L p ex) =
  case ex of
    -- Here the allocation has already been performed:
    -- To follow the calling convention, we are reponsible for tagging on the
    -- end here:
    VarE v -> do
      let ty = case M.lookup v tenv of
                 Just t -> t
                 Nothing -> error $ sdoc v ++ " not found."
      if isPackedTy ty
      then return $ mkDi (l$ VarE v) [ l$ VarE (toEndV v) ]
      else return $ dl $ VarE v

    LitE _n    -> error $ "Shouldn't encounter LitE in packed context:" ++ sdoc ex
    LitSymE _n -> error $ "Shouldn't encounter LitSymE in packed context:" ++ sdoc ex

    AppE{} -> dl <$> cursorizeAppE ddfs fundefs denv tenv (L p ex)

    -- DictLookup returns a packed value bound to a free location.
    -- PrimAppE (DictLookupP (PackedTy _ ploc)) vs ->
    --     do vs' <- forM vs $ \v -> cursorizeExp ddfs fundefs denv tenv v
    --        return $ mkDi (l$ PrimAppE (DictLookupP CursorTy) vs') [ l$ Ext NullCursor ]

    PrimAppE _ _ -> error $ "cursorizePackedExp: unexpected PrimAppE in packed context:" ++ sdoc ex

    -- The only (other) primitive that returns packed data is ReadPackedFile:
    -- This is simpler than TimeIt below.  While it's out-of-line,
    -- it doesn't need memory allocation (NewBuffer/ScopedBuffer).
    -- This is more like the witness case below.
    LetE (v,_locs, _ty, L _ (PrimAppE (ReadPackedFile path tyc reg ty2) [])) bod ->
       Di <$> cursorizeReadPackedFile ddfs fundefs denv tenv True v path tyc reg ty2 bod

    LetE (v,_locs,_ty, L sl (PrimAppE (DictLookupP (PackedTy _ ploc)) vs)) bod ->
        do vs' <- forM vs $ \v -> cursorizeExp ddfs fundefs denv tenv v
           let bnd = mkLets [(ploc, [], CursorTy, L sl (PrimAppE (DictLookupP CursorTy) vs'))
                            ,(v, [], CursorTy, l$ VarE ploc)]
               tenv' = M.insert ploc CursorTy $ M.insert v CursorTy tenv
           onDi bnd <$> go tenv' bod

    LetE (_v,_locs,_ty, (L _ (MkProdE _ls))) _bod ->
      dl <$> cursorizeProd True ddfs fundefs denv tenv ex

    LetE (_v,_locs,ty, (L _ ProjE{})) _bod | isPackedTy ty ->
      dl <$> cursorizeProj True ddfs fundefs denv tenv ex


    MkProdE ls -> do
      let tys = L.map (gRecoverType ddfs (Env2 tenv M.empty)) ls
      es <- forM (zip tys ls) $ \(ty,e) -> do
              case ty of
                  _ | isPackedTy ty -> fromDi <$> cursorizePackedExp ddfs fundefs denv tenv e
                  _ -> cursorizeExp ddfs fundefs denv tenv e
      let rhs' = l$ MkProdE es
      return $ Di rhs'

    LetE (_v,_locs,_ty, (L _ (ParE{}))) _bod ->
      dl <$> cursorizePar False ddfs fundefs denv tenv ex

    LetE bnd bod -> dl <$> cursorizeLet True ddfs fundefs denv tenv bnd bod

    -- Here we route the dest cursor to both braches.  We switch
    -- back to the other mode for the (non-packed) test condition.
    IfE a b c -> do
      Di b' <- go tenv b
      Di c' <- go tenv c
      a'    <- cursorizeExp ddfs fundefs denv tenv a
      return $ Di $ l $ IfE a' b' c'

    -- Not sure if we need to replicate all the checks from Cursorize1
    ProjE i e -> dl <$> ProjE i <$> fromDi <$> go tenv e

    -- A case expression is eventually transformed into a ReadTag + switch stmt.
    -- We first retrieve the cursor referred to by the scrutinee, and unpack
    -- the first bound variable 1 byte after that cursor. Thats all we need to do
    -- here, because we've already computed other locations in InferLocations and
    -- RouteEnds
    CaseE scrt brs -> do
      -- ASSUMPTION: scrutinee is always flat
      let (L _ (VarE v)) = scrt
      dl <$>
        CaseE (l$ VarE $ v) <$>
          mapM (unpackDataCon ddfs fundefs denv tenv True v) brs

    DataConE sloc dcon args -> do
      let
          -- Return (start,end) cursors
          -- The final return value lives at the position of the out cursors:
          go2 :: Var -> [(L Exp2, Ty2)] -> PassM Exp3
          go2 d [] = return $ MkProdE [l$ VarE sloc, l$ VarE d]

          go2 d ((rnd, ty):rst) = do
            d' <- gensym "writecur"
            case ty of
              _ | isPackedTy ty -> do
                 rnd' <- go tenv rnd
                 LetE (d',[], CursorTy, projEnds rnd') <$> l <$>
                   go2 d' rst

              -- Int, Sym, or Bool
              _ | isScalarTy ty -> do
                rnd' <- cursorizeExp ddfs fundefs denv tenv rnd
                LetE (d',[], CursorTy, l$ Ext $ WriteScalar (mkScalar ty) d rnd') <$> l <$>
                  go2 d' rst

              CursorTy -> do
                rnd' <- cursorizeExp ddfs fundefs denv tenv rnd
                LetE (d',[], CursorTy, l$ Ext $ WriteCursor d rnd') <$> l <$>
                  go2 d' rst
              _ -> error $ "Unknown type encounterred while cursorizing DataConE. Type was " ++ show ty

      writetag <- gensym "writetag"
      dl <$>
        LetE (writetag,[], CursorTy, l$ Ext $ WriteTag dcon sloc) <$> l <$>
          go2 writetag (zip args (lookupDataCon ddfs dcon))

    TimeIt e t b -> do
      Di e' <- go tenv e
      return $ dl$ TimeIt e' (cursorizeTy t) b

    WithArenaE v e -> do
      Di e' <- go (M.insert v ArenaTy tenv) e
      return $ dl$ WithArenaE v e'

    ParE a b -> do
       Di a' <- go tenv a
       Di b' <- go tenv b
       return $ dl$ ParE a' b'

    Ext ext ->
      case ext of

        -- All locations are transformed into cursors here. Location arithmetic
        -- is expressed in terms of corresponding cursor operations.
        -- See `cursorizeLocExp`
        LetLocE loc rhs bod -> do
          let rhs_either = cursorizeLocExp denv tenv loc rhs
              (bnds,tenv') = case M.lookup loc denv of
                               Nothing -> ([],tenv)
                               Just vs -> let extended = M.fromList [ (v,CursorTy) | (v,_,CursorTy,_) <- vs]
                                          in (vs, M.union extended tenv)
          case rhs_either of
            Right rhs' ->
              case M.lookup loc tenv of
                Nothing ->  onDi (mkLets ((loc,[],CursorTy,rhs') : bnds)) <$>
                              go (M.insert loc CursorTy tenv') bod
                Just _  -> go (M.insert loc CursorTy tenv') bod
            Left denv' -> onDi (mkLets bnds) <$>
                            cursorizePackedExp ddfs fundefs denv' tenv' bod
                            --

        -- ASSUMPTION: RetE forms are inserted at the tail position of functions,
        -- and we safely just return ends-witnesses & ends of the dilated expressions
        RetE locs v -> do
          v' <- go tenv (l$ VarE v)
          case locs of
            []    -> return v'
            [loc] -> return $ mkDi (l$ VarE loc) [ fromDi v' ]
            _ -> return $ Di $ l$ MkProdE $ L.foldr (\loc acc -> (l$ VarE loc):acc) [fromDi v'] locs

        LetRegionE r bod -> do
          onDi (mkLets (regionToBinds r)) <$> go tenv bod

        FromEndE{} -> error $ "cursorizePackedExp: TODO " ++ sdoc ext

        BoundsCheck i bound cur -> return <$> dl <$> Ext $ L3.BoundsCheck i bound cur

        IndirectionE _ dcon (pointer,r1) (pointee,r2) _ -> do
          dflags <- getDynFlags
          if gopt Opt_DisableGC dflags || (r1 == "dummy" || r2 == "dummy") -- HACK!!!
          then go tenv (l$ DataConE pointer dcon [l$ VarE pointee])
          else
            onDi (mkLets [("_",[],IntTy, l$ Ext (BumpRefCount (toEndV r1) (toEndV r2)))]) <$>
              go tenv (l$ DataConE pointer dcon [l$ VarE pointee])

    MapE{}  -> error $ "TODO: cursorizePackedExp MapE"
    FoldE{} -> error $ "TODO: cursorizePackedExp FoldE"

  where go = cursorizePackedExp ddfs fundefs denv
        dl = Di <$> L p


cursorizeReadPackedFile :: DDefs Ty2 -> FunDefs2 -> DepEnv -> M.Map Var (UrTy LocVar) -> Bool -> Var
                        -> Maybe FilePath -> TyCon -> Maybe Var -> Ty2 -> L Exp2
                        -> PassM (L (PreExp E3Ext () (UrTy ())))
cursorizeReadPackedFile ddfs fundefs denv tenv isPackedContext v path tyc reg ty2 bod = do
  case reg of
    Nothing -> error $ "cursorizePackedExp: InferLocations did not set the reg for ReadPackedFile."
    Just reg_var ->
      mkLets [ (v, [], CursorTy, l$ PrimAppE (toL3Prim $ ReadPackedFile path tyc reg ty2) [])
             , (reg_var, [], CursorTy, l$ VarE v)
             , (toEndV reg_var, [], CursorTy, l$ Ext$ AddCursor reg_var (l$ Ext $ MMapFileSize v))] <$>
         go (M.insert v CursorTy tenv) bod

  where
    go t e = if isPackedContext
             then fromDi <$> cursorizePackedExp ddfs fundefs denv t e
             else cursorizeExp ddfs fundefs denv t e

-- We may sometimes encounter a letloc which uses an unbound location.
--
--     letloc loc_b = loc_a + 1
--
-- i.e `loc_a` may not always be bound. If that's the case, don't process `loc_b`
-- now. Instead, add it to the dependency environment.
cursorizeLocExp :: DepEnv -> TyEnv Ty2 -> LocVar -> LocExp -> Either DepEnv (L Exp3)
cursorizeLocExp denv tenv lvar locExp =
  case locExp of
    AfterConstantLE i loc ->
      let rhs = l$ Ext $ AddCursor loc (l$ LitE i)
      in if isBound loc
         then Right rhs
         else Left$ M.insertWith (++) loc [(lvar,[],CursorTy,rhs)] denv
    -- TODO: handle product types here

{- [2018.03.07]:

Changing it's meaning to just be "after a variable", but not offset from any
particular location. Such an offset requires calculating the size of the variable.
For BigInfinite regions, this is simple:

    size = (endof v) - v

But Infinite regions do not support sizes yet. Re-enable this later.
-}
    AfterVariableLE v loc -> do
      let vty = case M.lookup v tenv of
                  Just ty -> ty
                  Nothing -> error $ "cursorizeLocExp: Var " ++ sdoc v ++ " not found."
          bod = case vty of
                  PackedTy{} -> l$ VarE (toEndV v)
                  CursorTy -> l$ VarE (toEndV v)
                  IntTy -> let sizeVar = varAppend "sizeof_" v
                               sizeVal = l$ Ext $ SizeOfScalar v
                               rhs = l$ Ext $ AddCursor loc (l$ VarE (sizeVar))
                           in mkLets [(sizeVar,[], IntTy, sizeVal)] rhs
                  oth -> error $ "cursorizeLocExp: AfterVariable TODO " ++ sdoc oth
      if isBound loc
      then Right bod
      else Left $ M.insertWith (++) loc
                  -- TODO: sizeVar is lost here...
                  [(lvar,[],CursorTy,bod)]
                  denv

    FromEndLE loc -> if isBound loc
                     then Right$ l$ VarE loc
                     else Left$ M.insertWith (++) loc [(lvar,[],CursorTy,l$ VarE loc)] denv
    StartOfLE r   -> case r of
                       GlobR v _ -> Right$ l$ VarE v
                       VarR v    -> Right$ l$ VarE v
                       DynR v _  -> Right$ l$ VarE v
                       -- TODO: docs
                       MMapR _v   -> Left$ denv

    FreeLE -> Left$ denv -- AUDIT: should we just throw away this information?

    InRegionLE{}  -> error $ "cursorizeExp: TODO InRegionLE"
  where
    isBound x = case M.lookup x tenv of
                  Just _  -> True
                  Nothing -> False

-- ASSUMPTIONS:
-- (1) `locs` has [in_regions, out_regions, in_locs, out_locs] for the function.
--     But after Cursorize, the calling convention changes so that input
--     locations appear last. Plus, `arg` would supply those. So we can
--     safely drop them from `locs`.
--
-- (2) We update `arg` so that all packed values in it only have start cursors.
cursorizeAppE :: DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> L Exp2 -> PassM Exp3
cursorizeAppE ddfs fundefs denv tenv (L _ ex) =
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
                            then fromDi <$> cursorizePackedExp ddfs fundefs denv tenv a
                            else cursorizeExp ddfs fundefs denv tenv a)
                 (zip in_tys args)
      starts <- pure $ map (uncurry giveStarts) (zip argTys args')
      case locs of
        [] -> return $ AppE f [] starts
        _  -> return $ AppE f [] ([l$ VarE loc | loc <- outs] ++ starts)
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
cursorizeProj :: Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> Exp2 -> PassM Exp3
cursorizeProj isPackedContext ddfs fundefs denv tenv ex =
  case ex of
    LetE (v,_locs,ty, rhs@(L _ ProjE{})) bod | isPackedTy ty -> do
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
      return $ unLoc $ mkLets bnds bod'

    _ -> error $ "cursorizeProj: Unexpected expression: " ++ sdoc ex

  where
    go t x = if isPackedContext
             then fromDi <$> cursorizePackedExp ddfs fundefs denv t x
             else cursorizeExp ddfs fundefs denv t x


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
cursorizeProd :: Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> Exp2 -> PassM Exp3
cursorizeProd isPackedContext ddfs fundefs denv tenv ex =
  case ex of
    LetE (v,_locs,ProdTy tys, rhs@(L _ (MkProdE ls))) bod -> do
      es <- forM (zip tys ls) $ \(ty,e) -> do
              case ty of
                  _ | isPackedTy ty -> fromDi <$> cursorizePackedExp ddfs fundefs denv tenv e
                  _ | hasPacked ty  -> error $ "cursorizePackedExp: nested tuples" ++ sdoc rhs
                  _ -> cursorizeExp ddfs fundefs denv tenv e
      let rhs' = l$ MkProdE es
          ty   = gRecoverType ddfs (Env2 tenv M.empty) rhs
          ty'  = cursorizeTy ty
          tenv' = M.insert v ty tenv
      bod' <- go tenv' bod
      return $ unLoc $ mkLets [(v,[], ty', rhs')] bod'

    _ -> error $ "cursorizeProj: Unexpected expression: " ++ sdoc ex

  where
    go t x = if isPackedContext
             then fromDi <$> cursorizePackedExp ddfs fundefs denv t x
             else cursorizeExp ddfs fundefs denv t x

{-

Cursorizing the parallel tuple combinator
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

ASSUMPTIONS:
    (1) ParE only has function calls as sub expressions.
    (2) It's OK if we don't bind the end-witnesses returned by these fns.
        (Most likely, this is a garbage assumption but OK for now.)

How is it cursorized ?

    If the functions in the parallel tuple return any end-witnesses;

    Then (1) Update the type of the let bound variable using gRecoverType
             (probably RouteEnds should do this step).
         (2) Bind the end-witnesses
         (3) Use projections and products to recover the original value
             (which doesn't include end-witnesses)

    Else Nothing special happens.


Projections off of parallel tuples
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Why don't we cursorize these projections like Note [Cursorizing projections] ?

i.e instead of direct projections like (#0 #1 tup), we generate

    let tmp = #1 tup
    in #0 tmp

TLDR: Because of the way Flatten, Unariser and Lower deal with parallel tuples.

..TODO (finish this note)..

-}
cursorizePar :: Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> Exp2 -> PassM L3.Exp3
cursorizePar isPackedContext ddfs fundefs denv tenv ex =
  case ex of
    LetE (v,locs, ProdTy [tya, tyb], rhs@(L _ (ParE a b))) bod ->
      case (a,b) of
        (L _ (AppE f _ _), L _ (AppE g _ _)) -> do
          tup   <- gensym "par_tup"
          (tya', bnds1, left, idx1) <- doapp tup locs f tya 0
          (tyb', bnds2, right, _)  <- doapp tup (L.drop idx1 locs) g tya 1
          rhs'  <- go tenv rhs
          let bnds = [ (tup,   [], ProdTy [tya', tyb'], rhs') ]
                     ++ bnds1 ++ bnds2 ++
                     [ (v,     [], ProdTy [stripTyLocs tya, stripTyLocs tyb],
                       l$ MkProdE [(l$ VarE left), (l$ VarE right)]) ]
          --TODO: Extend it with proper types of the bindings created before.
          let tenv' = M.union (M.fromList []) tenv
          bod' <- go tenv' bod
          return $ unLoc $ mkLets bnds bod'

        _ -> error $ "cursorizePar: Expected function calls, got: " ++ sdoc rhs

    _ -> error $ "cursorizePar: Unexpected expression: " ++ sdoc ex

  where
    -- After Cursorize, a function might return some end-witnesses along with the value.
    -- "doapp" ensures that "part" contains the return *value* which "cursorizePar" uses
    -- to stitch together the original tuple.
    doapp par_tup locs1 f ty idx = do
      let fnty = funTy (fundefs # f)
          retlocs = locVars fnty
          ty' = stripTyLocs ty
      part <- gensym "par_part"
      case retlocs of
        [] -> return (ty', [(part,[], ty', mkProj idx (l$ VarE par_tup))], part, 0)
        _  -> do
          -- See Note [Projections off of parallel tuples]
          tmp <- gensym "par_tmp"
          let (ty'', idx1) = tyWithWitnesses f ty
              bnds = [(tmp,  [], ty'', mkProj idx (l$ VarE par_tup))
                     ,(part, [], ty' , mkProj idx1 (l$ VarE tmp))] ++
                     [ (loc,[],CursorTy, mkProj i (l$ VarE tmp))
                     | (loc, i) <- zip (L.take idx1 locs1) [0..]]
          return (ty'', bnds, part, idx1)

    -- The *value* is after all the end-witnesses (length fnrets).
    tyWithWitnesses f oldty =
      let fnty = funTy (fundefs # f)
          fnrets = L.map (\_ -> CursorTy) (locRets fnty)
      in (stripTyLocs (ProdTy (fnrets ++ [oldty])), length fnrets)

    go t x = if isPackedContext
             then fromDi <$> cursorizePackedExp ddfs fundefs denv t x
             else cursorizeExp ddfs fundefs denv t x


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
cursorizeLet :: Bool -> DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2
             -> (Var, [Var], Ty2, L Exp2) -> L Exp2 -> PassM Exp3
cursorizeLet isPackedContext ddfs fundefs denv tenv (v,locs,ty,rhs) bod
    | isPackedTy ty = do
        rhs' <- fromDi <$> cursorizePackedExp ddfs fundefs denv tenv rhs
        fresh <- gensym "tup_packed"
        let ty' = case locs of
                    [] -> cursorizeTy ty
                    xs -> ProdTy ([CursorTy | _ <- xs] ++ [cursorizeTy ty])

            tenv' = L.foldr (\(a,b) acc -> M.insert a b acc) tenv $
                      [(v, ty),(fresh, ty'),(toEndV v, projTy 1 ty')] ++ [(loc,CursorTy) | loc <- locs]

            -- TyEnv Ty2 and L3 expresssions are tagged with different types
            ty''  = curDict $ stripTyLocs ty'
            rhs'' = l$ VarE fresh

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
        return $ unLoc $ mkLets bnds bod'

    | hasPacked ty = do
        rhs' <- fromDi <$> cursorizePackedExp ddfs fundefs denv tenv rhs
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
                        [(loc,[],CursorTy, l$ ProjE n (l$ VarE fresh)) | (loc,n) <- (zip locs [0..])]
                        ++ [(v,[], projTy (length locs) ty'', l$ ProjE (length locs) (l$ VarE fresh))]
            unLoc . mkLets bnds <$> go tenv'' bod

    | otherwise = do
        rhs' <- cursorizeExp ddfs fundefs denv tenv rhs
        case locs of
            [] -> LetE (v,[],curDict $ stripTyLocs ty, rhs') <$>
                    go (M.insert v ty tenv) bod
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
            [loc] -> do
              fresh <- gensym "tup_scalar"
              let ty'  = ProdTy ([CursorTy | _ <- locs] ++ [cursorizeTy ty])
                  -- We cannot resuse ty' here because TyEnv Ty2 and expresssions are
                  -- tagged with different
                  ty'' = stripTyLocs ty'
                  tenv' = M.union (M.fromList [(fresh, ty'),
                                               (loc, projTy 0 ty'),
                                               (v, projTy 1 ty')])
                          tenv
                  rhs'' = dl$ VarE fresh
                  bnds  = [ (fresh, [] , ty''          , rhs')
                          , (loc   ,[] , projTy 0 ty'' , projVal rhs'')
                          , (v     ,[] , projTy 1 ty'' , projEnds rhs'')
                          ]
              bod' <- go tenv' bod
              return $ unLoc $ mkLets bnds bod'
            _ -> error "cursorizeLet: packed tuples error2"

  where go t x = if isPackedContext
                 then fromDi <$> cursorizePackedExp ddfs fundefs denv t x
                 else cursorizeExp ddfs fundefs denv t x
        dl = Di <$> L NoLoc

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
unpackDataCon :: DDefs Ty2 -> FunDefs2 -> DepEnv -> TyEnv Ty2 -> Bool -> Var
              -> (DataCon, [(Var, Var)], L Exp2) -> PassM (DataCon, [t], L Exp3)
unpackDataCon ddfs fundefs denv1 tenv1 isPacked scrtCur (dcon,vlocs1,rhs) = do
  field_cur <- gensym "field_cur"

  (dcon, [],)
    -- Advance the cursor by 1 byte so that it points to the first field
    <$> mkLets [(field_cur,[],CursorTy, l$ Ext $ AddCursor scrtCur (l$ LitE 1))]
    <$> (if isIndrDataCon dcon
         then unpackWithRAN field_cur
         else unpackRegularDataCon field_cur)

  where
    tys1 = lookupDataCon ddfs dcon
    processRhs denv env = if isPacked
                          then fromDi <$> cursorizePackedExp ddfs fundefs denv env rhs
                          else cursorizeExp ddfs fundefs denv env rhs

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
    unpackRegularDataCon :: Var -> PassM (L Exp3)
    unpackRegularDataCon field_cur = go field_cur vlocs1 tys1 True denv1 (M.insert field_cur CursorTy tenv1)
      where
        go :: Var -> [(Var, LocVar)] -> [Ty2] -> Bool -> DepEnv -> TyEnv Ty2 -> PassM (L Exp3)
        go cur vlocs tys canBind denv tenv =
          case (vlocs, tys) of
            ([],[]) -> processRhs denv tenv
            ((v,loc):rst_vlocs, ty:rst_tys) ->
              case ty of
                -- Int, Sym, or Bool
                _ | isScalarTy ty -> do
                  (tenv', binds) <- scalarBinds ty v loc tenv
                  if canBind
                  then do
                    -- If the location exists in the environment, it indicates that the
                    -- corresponding variable was also bound and we shouldn't create duplicate
                    -- bindings (checked in the LetLocE cases).
                    let binds' = (loc,[],CursorTy, l$ VarE cur):binds
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
                    return $ mkLets [(loc, [], CursorTy, l$ VarE cur)
                                    ,(v  , [], CursorTy, l$ VarE loc)]
                             bod
                  else do
                    -- Cannot read this. Instead, we add it to DepEnv.
                    let denv' = M.insertWith (++) loc [(v,[],CursorTy,l$ VarE loc)] denv
                    go (toEndV v) rst_vlocs rst_tys False denv' tenv'

                _ -> error $ "unpackRegularDataCon: Unexpected field " ++ sdoc (v,loc) ++ ":" ++ sdoc ty

            _ -> error $ "unpackRegularDataCon: Unexpected numnber of varible, type pairs: " ++ show (vlocs,tys)

    -- We have access to all fields in this constructor, and can create
    -- bindings for everything. We begin by unpacking the random access nodes.
    unpackWithRAN :: Var -> PassM (L Exp3)
    unpackWithRAN field_cur =
        -- A map from a variable to a tuple containing it's location and
        -- the RAN field it depends on. Consider this constructor:
        --
        --     (Node^ [(ind_y3, loc_ind_y3), (n1, loc_n1) , (x2 , loc_x2), (y3 , loc_y3)] ...),
        --
        -- it will be the map:
        --
        --     (y3 -> (loc_y3, ind_y3))
        let ran_mp =
              case numRANsDataCon ddfs (fromIndrDataCon dcon) of
                0 -> M.empty
                n -> let -- Random access nodes occur immediately after the tag
                         ind_vars = L.map fst $ L.take n vlocs1
                         -- Everything else is a regular consturctor field,
                         -- which depends on some random access node
                         data_fields = L.take n (reverse vlocs1)
                         (vars, var_locs) = unzip data_fields
                     in M.fromList $ zip vars (zip var_locs ind_vars)
        in go field_cur vlocs1 tys1 ran_mp denv1 (M.insert field_cur CursorTy tenv1)
      where
        go :: Var -> [(Var, LocVar)] -> [Ty2] -> M.Map Var (Var,Var) -> DepEnv -> TyEnv Ty2 -> PassM (L Exp3)
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

                      binds = [(tmp     , [], ProdTy [CursorTy, CursorTy], l$ Ext $ ReadCursor cur),
                               (loc     , [], CursorTy, l$ VarE cur),
                               (v       , [], CursorTy, l$ ProjE 0 (l$ VarE tmp)),
                               (toEndV v, [], CursorTy, l$ ProjE 1 (l$ VarE tmp))]
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv'
                  return $ mkLets binds bod

                -- Int, Sym, or Bool
                _ | isScalarTy ty -> do
                  (tenv', binds) <- scalarBinds ty v loc tenv
                  let loc_bind = case M.lookup v indirections_env of
                                   -- This appears before the first packed field. Unpack it
                                   -- in the usual way.
                                   Nothing ->
                                     (loc,[],CursorTy, l$ VarE cur)
                                   -- We need to read this using a random access node
                                   Just (_var_loc, ind_var) ->
                                     (loc,[],CursorTy, l$ VarE ind_var)
                      binds' = loc_bind:binds
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
                                     (loc, [], CursorTy, l$ VarE cur)
                                   -- We need to access this using a random access node
                                   Just (_var_loc, ind_var) ->
                                     (loc, [], CursorTy, l$ VarE ind_var)
                  bod <- go (toEndV v) rst_vlocs rst_tys indirections_env denv tenv'
                  return $ mkLets [ loc_bind, (v, [], CursorTy, l$ VarE loc) ] bod

                _ -> error $ "unpackRegularDataCon: Unexpected field " ++ sdoc (v,loc) ++ ":" ++ sdoc ty

            _ -> error $ "unpackRegularDataCon: Unexpected numnber of varible, type pairs: " ++ show (vlocs,tys)

    -- Generate bindings for unpacking int fields. A convenient
    scalarBinds :: Ty2 -> Var -> LocVar -> TyEnv Ty2 -> PassM (TyEnv Ty2, [(Var, [()], Ty3, L Exp3)])
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

          binds = [(tmp     , [], ProdTy [ty', CursorTy], l$ Ext $ ReadScalar s loc),
                   (v       , [], ty'     , l$ ProjE 0 (l$ VarE tmp)),
                   (toEndV v, [], CursorTy, l$ ProjE 1 (l$ VarE tmp))]
      return (tenv', binds)

giveStarts :: Ty2 -> L Exp3 -> L Exp3
giveStarts ty e =
  case ty of
    PackedTy{} -> mkProj 0 e
    ProdTy tys -> case unLoc e of
                    MkProdE es -> l$ MkProdE $ L.map (\(ty',e') -> giveStarts ty' e') (zip tys es)
                    VarE{} -> l$ MkProdE $ L.map (\(ty',n) -> giveStarts ty' (mkProj n e)) (zip tys [0..])
                    -- This doesn't look right..
                    ProjE n x -> giveStarts (tys !! n) (mkProj 0 (mkProj n x))
                    oth -> error $ "giveStarts: unexpected expresson" ++ sdoc (oth,ty)
    _ -> e


projValTy :: (Out a) => UrTy a -> UrTy a
projValTy = projTy 0

projEndsTy :: (Out a) => UrTy a -> UrTy a
projEndsTy = projTy 1


-- | Bindings for a letregion
regionToBinds :: Region -> [(Var, [()], Ty3, L Exp3)]
regionToBinds r =
  case r of
    VarR{} -> error $ "Unexpected VarR in Cursorize." ++ sdoc r
    GlobR v mul -> [ (v       , [], CursorTy, l$ Ext$ NewBuffer mul)
                   , (toEndV v, [], CursorTy, l$ Ext$ AddCursor v (l$ Ext $ InitSizeOfBuffer mul))]
    DynR v mul  -> [ (v       , [], CursorTy, l$ Ext$ ScopedBuffer mul)
                   , (toEndV v, [], CursorTy, l$ Ext$ AddCursor v (l$ Ext $ InitSizeOfBuffer mul))]
    -- TODO: docs
    MMapR _v    -> []

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
projEnds :: DiExp (L Exp3) -> (L Exp3)
projEnds (Di e) = mkProj 1 e

-- | Project the original value from a dilated expression.
projVal :: DiExp (L Exp3) -> (L Exp3)
projVal (Di e) = mkProj 0 e

-- | Constructor that combines a regular expression with a list of
-- corresponding end cursors.
mkDi :: (L Exp3) -> [(L Exp3)] -> DiExp (L Exp3)
mkDi x []  = Di $ l$ MkProdE [x,l$ MkProdE []]
mkDi x [o] = Di $ l$ MkProdE [x, o]
mkDi x ls  = Di $ l$ MkProdE [x, l$ MkProdE ls]

curDict :: UrTy a -> UrTy a
curDict (SymDictTy ar _ty) = SymDictTy ar CursorTy
curDict ty = ty
