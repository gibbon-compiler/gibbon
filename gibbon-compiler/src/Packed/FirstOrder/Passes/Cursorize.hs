{-# LANGUAGE OverloadedStrings #-}

module Packed.FirstOrder.Passes.Cursorize
  (cursorize) where

import Control.Monad (forM)
import Data.Loc
import Data.List as L
import Data.Map as M
import Text.PrettyPrint.GenericPretty

import Packed.FirstOrder.GenericOps
import Packed.FirstOrder.Common    hiding (FunDefs, FunDef(..))
import Packed.FirstOrder.L1.Syntax hiding (Prog(..), FunDef(..), FunDefs)
import Packed.FirstOrder.L2.Syntax as L2
import qualified Packed.FirstOrder.L3.Syntax as L3

import Debug.Trace
--------------------------------------------------------------------------------


-- | Cursor insertion, strategy one.
--
-- Here we go to a "dilated" representation of packed values, where
-- every `Packed T` is represented by a pair, `(Cursor,Cursor)`,
-- i.e. start/end. Except function arguments, and variables bound by
-- by a pattern match. They're just `start` cursors.
--
-- REASONING: Why the dilated convention?  In a word: conditionals.  At the
-- end of each function body we need to return the appropriate end cursors.
-- But during the computation, we may need to add an arbitrary amount of
-- extra state to the return type of a conditional.  Thus it's difficult to
-- do this routing of information without changing the types of intermediate
-- expressions significantly.  Dilation is the current strategy.
--
-- We proceed with two loops, corresponding to packed and unpacked
-- context.  When the type of the current expression satisfies
-- `hasPacked`, that's when we're in packed context.  And, when in
-- packed context, we return dilated values.


type TEnv = M.Map Var Ty2


-- | Track variables depending on location variables.
--
--   If we have to create binding of the form `let v = loc` (in case expressions for example),
--   but `loc` is not bound yet, we'll add the variable to this map.
--   This is a stupid/simple way to get rid of FindWitnesses.
--   See `FindWitnesses.hs` for why that is needed.
type DepEnv = M.Map LocVar [(Var,[()],L3.Ty3,L L3.Exp3)]

-- |
cursorize :: Prog -> SyM L3.Prog
cursorize Prog{ddefs,fundefs,mainExp} = do
  fns' <- mapM (fd . snd) (M.toList fundefs)
  let fundefs' = M.fromList $ L.map (\f -> (L3.funname f, f)) fns'
      ddefs'   = M.map L3.eraseLocMarkers ddefs

  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (e,ty) -> do
                  if hasPacked ty
                  then Just . (, L3.stripTyLocs ty) <$>
                         fromDi <$> cursorizePackedExp ddefs fundefs M.empty M.empty e
                  else Just . (,L3.stripTyLocs ty) <$>
                         cursorizeExp ddefs fundefs M.empty M.empty e

  return $ L3.Prog ddefs' fundefs' mainExp'

  where
    fd :: FunDef -> SyM L3.FunDef
    fd FunDef{funname,funty,funarg,funbod} =
      let inLocs  = inLocVars funty
          outLocs = outLocVars funty

          inT    = arrIn funty
          outT   = arrOut funty
          funty' = L3.cursorizeArrowTy funty
      in do
       newarg <- gensym "newarg"
       -- Output cursors are always inserted before all other arguments. So we can
       -- binding all cursors at 0
       let outCurBinds = mkLets [ (cur,[],CursorTy, l$ ProjE i (l$ VarE newarg))
                                | (cur,i) <- zip outLocs [0..]]

           -- Create projections for input cursors. By our current conventions, input cursors are
           -- passed after output cursors
           newargExp  = nProj (length outLocs) newarg
           inCurBinds = case inLocs of
                          [] -> mkLets [(funarg,[],L3.stripTyLocs inT, newargExp)]
                          _  -> let projs = mkInProjs newargExp inT
                                    bnds  = [(loc,[],CursorTy,proj) | (loc,proj) <- zip inLocs projs]
                                            ++ [(funarg,[], cursorizeInTy inT, newargExp)]
                                in mkLets bnds

           initEnv = M.fromList $ [(funarg, cursorizeInTy inT)] ++ [(a,CursorTy) | (LRM a _ _) <- locVars funty]

       bod <- if hasPacked outT
              then fromDi <$> cursorizePackedExp ddefs fundefs M.empty initEnv funbod
              else cursorizeExp ddefs fundefs M.empty initEnv funbod
       ret <- return $ outCurBinds (inCurBinds bod)
       return $ L3.FunDef funname funty' newarg ret


    -- | The only difference between this and L3.cursorizeTy is that here,
    --   packed types are replaced by a single CursorTy instead of ProdTy [CursorTy, CursorTy].
    --   Because packed fn arguments are passed as only 'start' cursors.
    --   Whereas, everywhere else, packed values are a (start,end) tuple
    cursorizeInTy :: UrTy a -> UrTy b
    cursorizeInTy ty =
      case ty of
        IntTy     -> IntTy
        BoolTy    -> BoolTy
        ProdTy ls -> ProdTy $ L.map cursorizeInTy ls
        SymDictTy ty' -> SymDictTy $ cursorizeInTy ty'
        PackedTy{}    -> CursorTy
        ListTy ty'    -> ListTy $ cursorizeInTy ty'
        PtrTy -> PtrTy
        CursorTy -> CursorTy

    -- | Helper to avoid duplicate code in mkInProjs
    nProj :: Int -> Var -> L L3.Exp3
    nProj n arg = if n == 0
                  then (l$ VarE arg)
                  else mkProjE n (l$ VarE arg)


    -- | Build projections for packed values in the input type
    --   This is used to create bindings for input location variables.
    --
    -- >>> mkInProjs e (PackedTy "T" "l")
    -- [VarE (Var "funarg")]
    --
    -- >>> mkInProjs e (ProdTy [IntTy,PackedTy "T" "l"])
    -- [ProjE 1 VarE (Var "funarg")]
    --
    -- >>> mkInProje e (ProdTy [ProdTy [PackedTy "T" "l", PackedTy "T" "l"], IntTy])
    -- [ProjE 0 ProjE 0 e, ProjE 1 ProjE 0 e]
    --
    -- >>> mkInProje e (ProdTy [PackedTy "T" "l",
    --                          IntTy,
    --                          ProdTy [PackedTy "T" "l",
    --                                  ProdTy [PackedTy "T" "l", PackedTy "T" "l"]]])
    -- [ProjE 0 e,ProjE 0 ProjE 2 e,ProjE 0 ProjE 1 ProjE 2 e,ProjE 1 ProjE 1 ProjE 2 e]
    mkInProjs :: L L3.Exp3 -> Ty2 -> [L L3.Exp3]
    mkInProjs = go []
     where
       go acc e ty =
         case ty of
           PackedTy{} -> acc ++ [e]
           ProdTy tys -> L.foldl (\acc2 (ty',n) -> go acc2 (mkProjE n e) ty') acc (zip tys [0..])
           _ -> acc


-- | Cursorize expressions NOT producing `Packed` values
cursorizeExp :: DDefs Ty2 -> NewFuns -> DepEnv -> TEnv -> L Exp2 -> SyM (L L3.Exp3)
cursorizeExp ddfs fundefs denv tenv (L p ex) = L p <$>
  case ex of
    VarE v    -> return $ VarE v
    LitE n    -> return $ LitE n
    LitSymE n -> return $ LitSymE n

    AppE f _ arg -> do
      let fnTy   = case M.lookup f fundefs of
                     Just g -> funty g
                     Nothing -> error $ "Unknown function: " ++ sdoc f
          inT    = arrIn fnTy
          {-
          inLocs = inLocVars fnTy
          numOutRegs = 2 * length (outRegVars fnTy)
          -- Drop input locations, but keep everything else
          outs   = (take numOutRegs locs) ++  (drop numOutRegs $ drop (length inLocs) $ locs)
          -}
          argTy  = gTypeExp ddfs (Env2 tenv M.empty) arg
      arg' <- if hasPacked inT
              then fromDi <$> cursorizePackedExp ddfs fundefs denv tenv arg
              else cursorizeExp ddfs fundefs denv tenv arg
      starts <- return $ giveStarts argTy arg'
      return $ AppE f [] starts

    PrimAppE pr args -> PrimAppE (L3.toL3Prim pr) <$> mapM go args

    -- Same as `cursorizePackedExp`
    LetE (v,_locs,ProdTy tys, rhs@(L _ (MkProdE ls))) bod -> do
      es <- forM (zip tys ls) $ \(ty,e) -> do
              case ty of
                  _ | isPackedTy ty -> fromDi <$> cursorizePackedExp ddfs fundefs denv tenv e
                  _ | hasPacked ty  -> error $ "cursorizePackedExp: nested tuples" ++ sdoc rhs
                  _ -> cursorizeExp ddfs fundefs denv tenv e
      let rhs' = l$ MkProdE es
          ty   = gTypeExp ddfs (Env2 tenv M.empty) rhs
          ty'  = L3.cursorizeTy ty
      LetE (v,[],ty', rhs') <$>
        cursorizeExp ddfs fundefs denv (M.insert v ty' tenv) bod


    -- Same as `cursorizePackedExp`
    LetE (v,_locs,ty, rhs@(L _ ProjE{})) bod | isPackedTy ty -> do
      rhs' <- go rhs
      let ty'  = gTypeExp ddfs (Env2 tenv M.empty) rhs
          ty'' = L3.cursorizeTy ty'
          bnds = if isPackedTy ty'
                 then [ (v       ,[], projValTy ty'' , mkProjE 0 rhs')
                      , (toEndV v,[], projEndsTy ty'', mkProjE 1 rhs')
                      ]
                 else [(v,[], ty'', rhs')]

          tenv' = if isPackedTy ty'
                  then M.union (M.fromList [(v,ty'), (toEndV v, projEndsTy ty')]) tenv
                  else M.insert v ty' tenv
      bod' <- cursorizeExp ddfs fundefs denv tenv' bod
      return $ unLoc $ mkLets bnds bod'


    -- Same as `cursorizePackedExp`
    LetE bnd bod -> cursorizeLet ddfs fundefs denv tenv False bnd bod

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

    TimeIt e ty b -> TimeIt <$> go e <*> pure (L3.stripTyLocs ty) <*> pure b

    -- Eg. leftmost
    Ext ext ->
      case ext of
        RetE locs v ->
          case locs of
              []    -> return (VarE v)
              [loc] -> return $ MkProdE [l$ VarE loc, l$ VarE v]
              _ -> error $ "cursorizeExp: RetE todo "

        -- All locations are transformed into cursors here. All the location expressions
        -- are expressed in terms of corresponding cursor operations. See `cursorizeLocExp`
        LetLocE loc rhs bod -> do
          let rhs_either = cursorizeLocExp denv tenv loc rhs
              (bnds,tenv') = case M.lookup loc denv of
                               Nothing -> ([],tenv)
                               Just vs -> let extended = M.fromList [ (v,CursorTy) | (v,_,CursorTy,_) <- vs]
                                          in (vs, M.union extended tenv)
          case rhs_either of
            Right rhs' -> unLoc . mkLets ((loc,[],CursorTy,rhs') : bnds) <$>
                         cursorizeExp ddfs fundefs denv (M.insert loc CursorTy tenv') bod
            Left denv' -> unLoc <$> cursorizeExp ddfs fundefs denv' tenv' bod

        -- Exactly same as cursorizePackedExp
        LetRegionE reg bod -> do
          let (v,buf) = regionToBnd reg
          LetE (v,[],CursorTy, l$ Ext buf) <$>
            go bod

        _ -> error $ "TODO: cursorizeExp Ext: " ++ sdoc ext

    MapE{} -> error $ "TODO: cursorizeExp MapE"
    FoldE{} -> error $ "TODO: cursorizeExp FoldE"

  where
    go = cursorizeExp ddfs fundefs denv tenv
    toEndV = varAppend "end_"


-- Cursorize expressions producing `Packed` values
cursorizePackedExp :: DDefs Ty2 -> NewFuns -> DepEnv -> TEnv -> L Exp2 -> SyM (DiExp (L L3.Exp3))
cursorizePackedExp ddfs fundefs denv tenv (L p ex) =
  case ex of
    -- Here the allocation has already been performed:
    -- To follow the calling convention, we are reponsible for tagging on the end here:
    VarE v -> do
      let ty = case M.lookup v tenv of
                 Just t -> t
                 Nothing -> error $ sdoc v ++ " not found."
      if isPackedTy ty
      then return $ mkDi (l$ VarE v) [ l$ VarE (toEndV v) ]
      else return $ dl $ VarE v

    LitE _n    -> error $ "Shouldn't encounter LitE in packed context:" ++ sdoc ex
    LitSymE _n -> error $ "Shouldn't encounter LitSymE in packed context:" ++ sdoc ex

    -- ASSUMPTIONS:
    -- 1) `locs` has both input and output locations for the function. But at the call-site
    --    we only have to prepend output locations, as the packed values in the argument
    --    already have the input locations.
    --    So to get the output locations, we drop (length inLocs) from `locs`, assuming
    --    that they are ordered correctly (inputs before outputs)
    --
    -- 2) We update `arg` so that all packed values in it only have start cursors.
    AppE f locs arg -> do
      let fnTy   = case M.lookup f fundefs of
                     Just g -> funty g
                     Nothing -> error $ "Unknown function: " ++ sdoc f
          inT    = arrIn fnTy
          inLocs = inLocVars fnTy
          outs   = L.drop (length inLocs) locs
          argTy  = gTypeExp ddfs (Env2 tenv M.empty) arg
      arg' <- if hasPacked inT
              then fromDi <$> go tenv arg
              else cursorizeExp ddfs fundefs denv tenv arg
      starts <- return $ giveStarts argTy arg'
      return $ dl$ AppE f [] $ l$ MkProdE $ [l$ VarE loc | loc <- outs] ++ [starts]


    PrimAppE _ _ -> error $ "cursorizePackedExp: unexpected PrimAppE in packed context" ++ sdoc ex

    -- The only primitive that returns packed data is ReadPackedFile:
    -- This is simpler than TimeIt below.  While it's out-of-line,
    -- it doesn't need memory allocation (NewBuffer/ScopedBuffer).
    -- This is more like the witness case below.
    LetE (vr,_locs, _ty, L _ (PrimAppE (ReadPackedFile path tyc ty2) [])) bod ->
      onDi (l <$> LetE (vr, [], CursorTy, l$ PrimAppE (L3.toL3Prim $ ReadPackedFile path tyc ty2) [])) <$>
        go (M.insert vr CursorTy tenv) bod



    -- NOTE: Products and projections:
    -- As per the dilated representation, all packed values are (start,end) tuples.
    -- Except fn arguments and pattern matched vars. They're represented by just start cursors.
    -- So instead of using the type from the AST, which will always be `Packed`, we recover
    -- type of RHS in the current type environment, using gTypeExp.
    -- If it's just `CursorTy`, this packed value doesn't have an end cursor.
    -- Otherwise, the type is `PackedTy{}`, and it has an end cursor.
    -- TODO: merge this with `cursorizeLet`
    LetE (v,_locs,ProdTy tys, rhs@(L _ (MkProdE ls))) bod -> do
      es <- forM (zip tys ls) $ \(ty,e) -> do
              case ty of
                  _ | isPackedTy ty -> fromDi <$> cursorizePackedExp ddfs fundefs denv tenv e
                  _ | hasPacked ty  -> error $ "cursorizePackedExp: nested tuples" ++ sdoc rhs
                  _ -> cursorizeExp ddfs fundefs denv tenv e
      let rhs' = l$ MkProdE es
          ty   = gTypeExp ddfs (Env2 tenv M.empty) rhs
          ty'  = L3.cursorizeTy ty
      onDi (l <$> LetE (v,[],ty', rhs')) <$>
        go (M.insert v ty tenv) bod


    -- Two ways in which we can cursorize this:
    --
    -- let pakd_tup = projE n something in
    -- let x        = projE 0 pakd_tup in
    -- let end_x    = projE 1 pakd_tup
    --
    -- OR
    --
    -- let x     = projE 0 (projE n something) in
    -- let end_x = projE 1 (projE n something)
    --
    -- `cursorizeLet` creates the former, while our special case here outputs the latter.
    -- Reason: unariser can only eliminate direct projections of this form
    LetE (v,_locs,ty, rhs@(L _ ProjE{})) bod | isPackedTy ty -> do
      rhs' <- fromDi <$> go tenv rhs
      let ty'  = gTypeExp ddfs (Env2 tenv M.empty) rhs
          ty'' = L3.cursorizeTy ty'
          bnds = if isPackedTy ty'
                 then [ (v       ,[], projValTy ty'' , mkProjE 0 rhs')
                      , (toEndV v,[], projEndsTy ty'', mkProjE 1 rhs')
                      ]
                 else [(v,[], ty'', rhs')]

          tenv' = if isPackedTy ty'
                  then M.union (M.fromList [(v,ty'), (toEndV v, projEndsTy ty')]) tenv
                  else M.insert v ty' tenv
      bod' <- fromDi <$> go tenv' bod
      return $ Di $ mkLets bnds bod'


    MkProdE ls -> do
      let tys = L.map (gTypeExp ddfs (Env2 tenv M.empty)) ls
      es <- forM (zip tys ls) $ \(ty,e) -> do
              case ty of
                  _ | isPackedTy ty -> fromDi <$> cursorizePackedExp ddfs fundefs denv tenv e
                  _ -> cursorizeExp ddfs fundefs denv tenv e
      let rhs' = l$ MkProdE es
      return $ Di rhs'

    LetE bnd bod -> dl <$> cursorizeLet ddfs fundefs denv tenv True bnd bod

    -- Here we route the dest cursor to both braches.  We switch
    -- back to the other mode for the (non-packed) test condition.
    IfE a b c -> do
      Di b' <- go tenv b
      Di c' <- go tenv c
      a'    <- cursorizeExp ddfs fundefs denv tenv a
      return $ Di $ l $ IfE a' b' c'

    -- Not sure if we need to replicate all the checks from Cursorize1
    ProjE i e -> dl <$> ProjE i <$> fromDi <$> go tenv e

    -- A case expression is eventually transformed into a ReadTag + switch statement.
    -- We first retrieve the cursor referred to by the scrutinee, and unpack
    -- the first bound variable 1 byte after that cursor. Thats all we need to do here,
    -- because we've already computed other locations in InferLocations and RouteEnds
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
          go2 :: Var -> [(L Exp2, Ty2)] -> SyM L3.Exp3
          go2 d [] = return $ MkProdE [l$ VarE sloc, l$ VarE d]

          go2 d ((rnd, ty):rst) = do
            d' <- gensym "writecur"
            if isPackedTy ty

            then do
             rnd' <- go tenv rnd
             LetE (d',[], CursorTy, projEnds rnd') <$> l <$>
               go2 d' rst

            -- INT is the only scalar type right now
            else do
             rnd' <- cursorizeExp ddfs fundefs denv tenv rnd
             LetE (d',[], CursorTy, l$ Ext $ L3.WriteInt d rnd') <$> l <$>
               go2 d' rst

      writetag <- gensym "writetag"
      dl <$>
        LetE (writetag,[], CursorTy, l$ Ext $ L3.WriteTag dcon sloc) <$> l <$>
          go2 writetag (zip args (lookupDataCon ddfs dcon))

    TimeIt e t b -> do
      Di e' <- go tenv e
      return $ Di $ l$ TimeIt e' (L3.stripTyLocs t) b

    Ext ext ->
      case ext of

        -- All locations are transformed into cursors here. All the location expressions
        -- are expressed in terms of corresponding cursor operations. See `cursorizeLocExp`
        LetLocE loc rhs bod -> do
          let rhs_either = cursorizeLocExp denv tenv loc rhs
              (bnds,tenv') = case M.lookup loc denv of
                               Nothing -> ([],tenv)
                               Just vs -> let extended = M.fromList [ (v,CursorTy) | (v,_,CursorTy,_) <- vs]
                                          in (vs, M.union extended tenv)
          case rhs_either of
            Right rhs' -> onDi (mkLets ((loc,[],CursorTy,rhs') : bnds)) <$>
                         go (M.insert loc CursorTy tenv') bod
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
            _ -> return $ Di $ l$ MkProdE $ L.foldl (\acc loc -> (l$ VarE loc):acc) [fromDi v'] locs

        LetRegionE r bod -> do
          let (v,buf) = regionToBnd r
          dl <$>
            LetE (v,[],CursorTy, l$ Ext buf) <$>
              fromDi <$> go tenv bod

        _ -> trace ("TODO: cursorizeExp:\n" ++ sdoc ext) (return $ Di $ l$  VarE (toVar $ sdoc ext))


    MapE{}  -> error $ "TODO: cursorizePackedExp MapE"
    FoldE{} -> error $ "TODO: cursorizePackedExp FoldE"

  where go = cursorizePackedExp ddfs fundefs denv
        toEndV = varAppend "end_"
        dl = Di <$> L p


{- Handle out-of-order letlocs:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We may sometimes encounter a letloc which uses an unbound location.

    letloc loc_b = loc_a + 1

i.e `loc_a` may not always be bound. If `loc_a` is unbound, don't process `loc_b`
now. Instead, add it to the dependency map.

-}
cursorizeLocExp :: DepEnv -> TEnv -> LocVar -> LocExp -> Either DepEnv (L L3.Exp3)
cursorizeLocExp denv tenv lvar locExp =
  case locExp of
    AfterConstantLE i loc ->
      let rhs = l$ Ext $ L3.AddCursor loc (l$ LitE i)
      in if isBound loc
         then Right rhs
         else Left$ M.insertWith (++) loc [(lvar,[],CursorTy,rhs)] denv
    -- TODO: handle product types here
    AfterVariableLE v loc ->
      let vty = case M.lookup v tenv of
                  Just ty -> ty
                  Nothing -> error $ "cursorizeLocExp: Var " ++ sdoc v ++ " not found."
          sizeVar = varAppend "sizeof_" v
          endVar  = varAppend "end_" v
          sizeVal = case vty of
                    PackedTy{} -> l$ Ext $ L3.SizeOfPacked v endVar
                    _          -> l$ Ext $ L3.SizeOfScalar v
          bod = l$ Ext $ L3.AddCursor loc (l$ VarE (sizeVar))
      in if isBound loc
         then Right$ mkLets [(sizeVar,[], IntTy, sizeVal)] bod
         else Left $ M.insertWith (++) loc
                     -- TODO: sizeVar is lost here...
                     [(lvar,[],CursorTy,bod)]
                     denv

    FromEndLE loc -> if isBound loc
                     then Right$ l$ VarE loc
                     else Left$ M.insertWith (++) loc [(lvar,[],CursorTy,l$ VarE loc)] denv
    StartOfLE r   -> Right$ case r of
                       GlobR v -> l$ VarE v
                       VarR v  -> l$ VarE v
                       DynR v  -> l$ VarE v
    InRegionLE{}  -> error $ "cursorizeExp: TODO InRegionLE"
  where
    isBound x = case M.lookup x tenv of
                  Just _  -> True
                  Nothing -> False

cursorizeLet :: DDefs Ty2 -> NewFuns -> DepEnv -> TEnv -> Bool
             -> (Var, [Var], Ty2, L Exp2) -> L Exp2 -> SyM L3.Exp3
cursorizeLet ddfs fundefs denv tenv isPackedContext (v,locs,ty,rhs) bod
    -- Process RHS and bind the following cursors
    --
    -- v     -> start_write
    -- end_v -> end_write
    -- loc   -> end_read (only if it's available)
    --
    -- An expression returning packed value can either be a `DataConE` or a `AppE`.
    -- DataConE returns a (start_write,end_write) tuple where AppE returns (end_read,end_write)
    --
    -- So we cannot always rely on the RHS to return a start_write cursor.
    -- But since the types of all packed expressions are already annotated with locations,
    -- we can take a shortcut here and directly bind `v` to the tagged location.
    --
    -- Other bindings are straightforward projections of the processed RHS.
    --
    | isPackedTy ty = do
        rhs' <- fromDi <$> cursorizePackedExp ddfs fundefs denv tenv rhs
        fresh <- gensym "tup_packed"
        let ty' = case locs of
                    [] -> L3.cursorizeTy ty
                    xs -> ProdTy ([CursorTy | _ <- xs] ++ [L3.cursorizeTy ty])

            tenv' = L.foldr (\(a,b) acc -> M.insert a b acc) tenv $
                       [(v, ty),(fresh, ty'),(toEndV v, projTy 1 ty')] ++ [(loc,CursorTy) | loc <- locs]

            -- Sigh .. We cannot resuse ty' here because TEnv and expresssions are tagged with different
            ty''  = case locs of
                      [] -> L3.cursorizeTy ty
                      xs -> ProdTy ([CursorTy | _ <- xs] ++ [L3.cursorizeTy ty])
            rhs'' = l$ VarE fresh

            bnds = case locs of
                      []    -> [ (fresh   , [], ty''          , rhs' )
                               , (v       , [], projTy 0 ty'' , mkProjE 0 rhs'')
                               , (toEndV v, [], projTy 1 ty'' , mkProjE 1 rhs'')]

                      _ -> let nLocs = length locs
                               locBnds = [(loc  ,[], CursorTy, mkProjE n rhs'')
                                         | (loc,n) <- zip locs [0..]]
                               bnds' = [(fresh   ,[], ty''                         , rhs')
                                       ,(v       ,[], projTy 0 $ projTy nLocs ty'' , mkProjE 0 $ mkProjE nLocs rhs'')
                                       ,(toEndV v,[], projTy 1 $ projTy nLocs ty'' , mkProjE 1 $ mkProjE nLocs rhs'')]
                           in bnds' ++ locBnds
        case M.lookup (toEndV v) denv of
          Just xs -> error $ "todo: " ++ sdoc xs
          Nothing -> return ()
        bod' <- go tenv' bod
        return $ unLoc $ mkLets bnds bod'

    | hasPacked ty = do
        rhs' <- fromDi <$> cursorizePackedExp ddfs fundefs denv tenv rhs
        let ty' = L3.cursorizeTy ty
            tenv' = M.union (M.insert v ty tenv) (M.fromList [(loc,CursorTy) | loc <- locs])
        case locs of
          [] -> LetE (v,[], ty', rhs') <$>
                  go tenv' bod
          _  -> do
            let bnds  = [(loc,[],CursorTy, l$ ProjE n rhs') | (loc,n) <- (zip locs [0..])]
                        ++ [(v,[],ty', l$ ProjE (length locs) rhs')]
            unLoc . mkLets bnds <$> go tenv' bod

    | otherwise = do
        rhs' <- cursorizeExp ddfs fundefs denv tenv rhs
        case locs of
            [] -> LetE (v,[],L3.stripTyLocs ty, rhs') <$>
                    go (M.insert v ty tenv) bod

            -- This was a scalar binding before, but now has been transformed to also
            -- return an end_read cursor. So the type of the binding now becomes:
            -- ProdTy [CursorTy, old_ty]
            --
            -- Also, the binding itself now changes to:
            -- end_read -> ProjE 0 RHS'
            -- v        -> ProjE 1 RHS'
            --
            -- `rightmost` is an example of a program that does this
            [loc] -> do
              fresh <- gensym "tup_scalar"
              let ty'  = ProdTy ([CursorTy | _ <- locs] ++ [L3.cursorizeTy ty])
                  -- We cannot resuse ty' here because TEnv and expresssions are tagged with different
                  ty'' = ProdTy ([CursorTy | _ <- locs] ++ [L3.cursorizeTy ty])
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
        toEndV = varAppend "end_"
        dl = Di <$> L NoLoc


-- | Take a cursor pointing to the start of the tag, and advance it by 1 byte
-- If the first bound varaible is a scalar (IntTy), read it using the newly returned cursor.
-- Otherwise, just process the body. it'll have the correct instructions to process
-- other bound locations
unpackDataCon :: DDefs Ty2 -> NewFuns -> DepEnv -> TEnv -> Bool -> Var
              -> (DataCon, [(Var, Var)], L Exp2) -> SyM (DataCon, [t], L L3.Exp3)
unpackDataCon ddfs fundefs denv1 tenv isPacked scrtCur (dcon,vlocs,rhs) = do
  -- The first bound location requires special handling. We have to bind it to
  -- (scrtCur + 1) by hand. All the other locations are bound (calculated) by RouteEnd2
  -- Ideally we should arrange RE to bind this as well, but this is a quick hack for now
  --
  cur <- gensym scrtCur
  (dcon,[],)
    <$> mkLets [(cur,[],CursorTy, l$ Ext $ L3.AddCursor scrtCur (l$ LitE 1))]
    <$> go cur vlocs tys True denv1 (M.insert cur CursorTy tenv)

  where -- (vars,locs) = unzip vlocs
        tys  = lookupDataCon ddfs dcon
        toEndV = varAppend "end_"
        processRhs denv env = if isPacked
                              then fromDi <$> cursorizePackedExp ddfs fundefs denv env rhs
                              else cursorizeExp ddfs fundefs denv env rhs

        -- Loop over fields.  Issue reads to get out all Ints. Otherwise, just bind vars to locations
        --
        go :: (Show t) => Var -> [(Var, Var)] -> [UrTy t] -> Bool -> DepEnv -> TEnv -> SyM (L L3.Exp3)
        go _c [] [] _isFirst denv env = processRhs denv env
        go cur ((v,loc):rst) (ty:rtys) canBind denv env =
          case ty of
            IntTy -> do
              tmp <- gensym (toVar "readint_tpl")
              let env' = M.union (M.fromList [(tmp     , ProdTy [IntTy, CursorTy]),
                                              (v       , IntTy),
                                              (toEndV v, CursorTy)])
                         env

                  bnds = [(tmp     , [], ProdTy [IntTy, CursorTy], l$ Ext $ L3.ReadInt loc),
                          (v       , [], IntTy   , l$ ProjE 0 (l$ VarE tmp)),
                          (toEndV v, [], CursorTy, l$ ProjE 1 (l$ VarE tmp))]

              if canBind
              then do
                let bnds' = (loc,[],CursorTy, l$ VarE cur):bnds
                    env'' = M.insert loc CursorTy env'
                bod <- go (toEndV v) rst rtys canBind denv env''
                return $ mkLets bnds' bod
              else do
                let denv'' = M.insertWith (++) loc bnds denv
                go (toEndV v) rst rtys canBind denv'' env'

            _ -> do
              let env' = M.insert v CursorTy env
              if canBind
              then do
                bod <- go (toEndV v) rst rtys False denv (M.insert loc CursorTy env')
                return $ mkLets [(loc, [], CursorTy, l$ VarE cur)
                                ,(v  , [], CursorTy, l$ VarE loc)]
                         bod
              else do
                -- Don't create a `let v = loc` binding. Instead, add it to DepEnv
                let denv'' = M.insertWith (++) loc [(v,[],CursorTy,l$ VarE loc)] denv
                go (toEndV v) rst rtys False denv'' env'

        go _ vls rtys _ _ _ = error $ "Unexpected numnber of varible, type pairs: " ++ show (vls,rtys)


-- |
giveStarts :: Ty2 -> L L3.Exp3 -> L L3.Exp3
giveStarts ty e =
  case ty of
    PackedTy{} -> mkProjE 0 e
    ProdTy tys -> case unLoc e of
                    MkProdE es -> l$ MkProdE $ L.map (\(ty',e') -> giveStarts ty' e') (zip tys es)
                    VarE{} -> l$ MkProdE $ L.map (\(ty',n) -> giveStarts ty' (mkProjE n e)) (zip tys [0..])
                    -- This doesn't look right..
                    ProjE n x -> giveStarts (tys !! n) (mkProjE 0 (mkProjE n x))
                    oth -> error $ "giveStarts: unexpected expresson" ++ sdoc (oth,ty)
    _ -> e


-- | Smart constructor that immediately destroys products if it can:
--   Does NOT avoid single-element tuples.
mkProjE :: Int -> (L L3.Exp3) -> (L L3.Exp3)
mkProjE ix (L _ (MkProdE ls)) = ls !! ix
mkProjE ix e = l$ (ProjE ix e)

projValTy :: (Out a) => UrTy a -> UrTy a
projValTy = projTy 0

projEndsTy :: (Out a) => UrTy a -> UrTy a
projEndsTy = projTy 1


-- | Return details to create a L3 binding for a region (var name and L3 extension)
regionToBnd :: Region -> (Var, L3.E3Ext loc dec)
regionToBnd r = case r of
                  GlobR v -> (v,L3.NewBuffer)
                  VarR  v -> (v,L3.NewBuffer)
                  DynR  v -> (v,L3.ScopedBuffer)


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
projEnds :: DiExp (L L3.Exp3) -> (L L3.Exp3)
projEnds (Di e) = mkProjE 1 e

-- | Project the original value from a dilated expression.
projVal :: DiExp (L L3.Exp3) -> (L L3.Exp3)
projVal (Di e) = mkProjE 0 e

-- | Constructor that combines a regular expression with a list of
-- corresponding end cursors.
mkDi :: (L L3.Exp3) -> [(L L3.Exp3)] -> DiExp (L L3.Exp3)
mkDi x []  = Di $ l$ MkProdE [x, l$ MkProdE []]
mkDi x [o] = Di $ l$  MkProdE [x, o]
mkDi x ls  = Di $ l$ MkProdE [x, l$ MkProdE ls]



{-

-- | For non-cursor types, dilation is very simple:
dilateTrivial :: ex -> DiExp ex
dilateTrivial e = Di $ MkProdE [e, MkProdE []]


-}
