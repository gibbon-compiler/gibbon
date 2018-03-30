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

{- Note: Cursor insertion, strategy one:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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


Consider a function add1:

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
  fns' <- mapM (cursorizeFunDef ddefs fundefs . snd) (M.toList fundefs)
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

-- |
cursorizeFunDef :: DDefs Ty2 -> NewFuns ->  FunDef -> SyM L3.FunDef
cursorizeFunDef ddefs fundefs FunDef{funname,funty,funarg,funbod} =
  let inLocs  = inLocVars funty
      outLocs = outLocVars funty
      outRegs = outRegVars funty
      inRegs  = inRegVars funty
      inT     = arrIn funty
      outT    = arrOut funty
      funty'  = cursorizeArrowTy funty
  in do
   newarg <- gensym "newarg"

   let
       totalRegs = length inRegs + length outRegs

       -- Input & output regions are always inserted before all other arguments.
       regBinds =  mkLets [ (toEndV reg, [], CursorTy, l$ ProjE i (l$ VarE newarg))
                          | (reg, i) <- zip (inRegs ++ outRegs) [0..]]

       -- Output cursors after that.
       outCurBinds = regBinds .
                     mkLets [ (cur,[],CursorTy, l$ ProjE i (l$ VarE newarg))
                            | (cur,i) <- zip outLocs [totalRegs..]]

       -- Then the input cursors. Create projections for input cursors here
       afterOutLocs  = nProj (totalRegs + length outLocs) newarg
       inCurBinds = case inLocs of
                      [] -> mkLets [(funarg,[],L3.stripTyLocs inT, afterOutLocs)]
                      _  -> let projs = mkInProjs afterOutLocs inT
                                bnds  = [(loc,[],CursorTy,proj) | (loc,proj) <- zip inLocs projs]
                                        ++ [(funarg,[], cursorizeInTy inT, afterOutLocs)]
                            in mkLets bnds

       initTyEnv = M.fromList $ [(funarg, cursorizeInTy inT)] ++ [(a,CursorTy) | (LRM a _ _) <- locVars funty]

   bod <- if hasPacked outT
          then fromDi <$> cursorizePackedExp ddefs fundefs M.empty initTyEnv funbod
          else cursorizeExp ddefs fundefs M.empty initTyEnv funbod
   ret <- return $ outCurBinds (inCurBinds bod)
   return $ L3.FunDef funname funty' newarg ret

  where
    -- | The only difference between this and L3.cursorizeTy is that here,
    --   packed types are replaced by a single CursorTy instead of
    --   a tuple (CursorTy,CursorTy). This is because only `start` cursors are
    --   passed in for packed function arguments.
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
    --
    mkInProjs :: L L3.Exp3 -> Ty2 -> [L L3.Exp3]
    mkInProjs = go []
     where
       go acc e ty =
         case ty of
           PackedTy{} -> acc ++ [e]
           ProdTy tys -> L.foldl (\acc2 (ty',n) -> go acc2 (mkProjE n e) ty')
                                 acc (zip tys [0..])
           _ -> acc

    cursorizeArrowTy :: L2.ArrowTy L2.Ty2 -> L3.ArrowTy L3.Ty3
    cursorizeArrowTy ty@L2.ArrowTy{L2.arrIn,L2.arrOut,L2.locVars,L2.locRets} =
      let
          -- Regions corresponding to ouput cursors. (See Note [Infinite regions])
          numOutRegs = length (L2.outRegVars ty)
          regs = L.map (\_ -> CursorTy) [1..numOutRegs]

          -- Adding additional outputs corresponding to end-of-input-value witnesses
          -- We've already computed additional location return value in RouteEnds
          rets = L.map (\_ -> CursorTy) locRets
          outT = L2.prependArgs (regs ++ rets) arrOut

          -- Packed types in the output then become end-cursors for those same destinations.
          newOut = L2.mapPacked (\_ _ -> ProdTy [CursorTy, CursorTy]) outT

          -- Adding additional input arguments for the destination cursors to which outputs
          -- are written.
          outCurs = L.filter (\(LRM _ _ m) -> m == Output) locVars
          outCurTys = L.map (\_ -> CursorTy) outCurs
          inRegs = L.map (\_ -> CursorTy) (L2.inRegVars ty)
          inT      = L2.prependArgs (inRegs ++ regs ++ outCurTys) arrIn

          -- Packed types in the input now become (read-only) cursors.
          newIn    = L2.mapPacked (\_ _ -> CursorTy) inT

      in L3.ArrowTy { L3.arrIn = L3.stripTyLocs newIn, L3.arrOut = L3.stripTyLocs newOut }


-- | Cursorize expressions NOT producing `Packed` values
cursorizeExp :: DDefs Ty2 -> NewFuns -> DepEnv -> TEnv -> L Exp2 -> SyM (L L3.Exp3)
cursorizeExp ddfs fundefs denv tenv (L p ex) = L p <$>
  case ex of
    VarE v    -> return $ VarE v
    LitE n    -> return $ LitE n
    LitSymE n -> return $ LitSymE n

    AppE{} -> cursorizeAppE ddfs fundefs denv tenv (L p ex)

    PrimAppE PEndOf [arg] -> do
      let (L _ (VarE v)) = arg
      return $ VarE (toEndV v)

    PrimAppE pr args -> PrimAppE (L3.toL3Prim pr) <$> mapM go args

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
            Right rhs' -> unLoc . mkLets ((loc,[],CursorTy,rhs') : bnds) <$>
                         cursorizeExp ddfs fundefs denv (M.insert loc CursorTy tenv') bod
            Left denv' -> unLoc <$> cursorizeExp ddfs fundefs denv' tenv' bod

        -- Exactly same as cursorizePackedExp
        LetRegionE reg bod -> do
          unLoc <$> mkLets (regionToBnds reg) <$> go bod

        BoundsCheck i bound cur -> return $ Ext $ L3.BoundsCheck i bound cur

        FromEndE{} -> error $ "cursorizeExp: TODO FromEndE" ++ sdoc ext

        IndirectionE{} -> error $ "cursorizeExp: Unexpected IndirectionE"

    MapE{} -> error $ "TODO: cursorizeExp MapE"
    FoldE{} -> error $ "TODO: cursorizeExp FoldE"

  where
    go = cursorizeExp ddfs fundefs denv tenv


-- Cursorize expressions producing `Packed` values
cursorizePackedExp :: DDefs Ty2 -> NewFuns -> DepEnv -> TEnv -> L Exp2
                   -> SyM (DiExp (L L3.Exp3))
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

    PrimAppE _ _ -> error $ "cursorizePackedExp: unexpected PrimAppE in packed context" ++ sdoc ex

    -- The only primitive that returns packed data is ReadPackedFile:
    -- This is simpler than TimeIt below.  While it's out-of-line,
    -- it doesn't need memory allocation (NewBuffer/ScopedBuffer).
    -- This is more like the witness case below.
    LetE (vr,_locs, _ty, L _ (PrimAppE (ReadPackedFile path tyc ty2) [])) bod ->
      onDi (l <$> LetE (vr, [], CursorTy, l$ PrimAppE (L3.toL3Prim $ ReadPackedFile path tyc ty2) [])) <$>
        go (M.insert vr CursorTy tenv) bod


{- Note [Products and projections]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

As per the dilated representation, all packed values are (start,end) tuples.
Except fn arguments and pattern matched vars. They're represented by just start
cursors. So instead of using the type from the AST, which will always be `Packed`,
we recover type of RHS in the current type environment, using gTypeExp.
If it's just `CursorTy`, this packed value doesn't have an end cursor.
Otherwise, the type is `PackedTy{}`, and it has an end cursor.
TODO: merge this with `cursorizeLet`

-}
    LetE (v,_locs,ProdTy tys, rhs@(L _ (MkProdE ls))) bod -> do
      es <- forM (zip tys ls) $ \(ty,e) -> do
              case ty of
                  _ | isPackedTy ty -> fromDi <$> cursorizePackedExp ddfs fundefs denv tenv e
                  _ | forgivingHasPacked ty  -> error $ "cursorizePackedExp: nested tuples" ++ sdoc rhs
                  _ -> cursorizeExp ddfs fundefs denv tenv e
      let rhs' = l$ MkProdE es
          ty   = gTypeExp ddfs (Env2 tenv M.empty) rhs
          ty'  = L3.cursorizeTy ty
      onDi (l <$> LetE (v,[],ty', rhs')) <$>
        go (M.insert v ty tenv) bod

{- Note [Cursorizing projections]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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


    MkProdE{} -> error "cursorizePackedExp: unexpected MkProdE"

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
          go2 :: Var -> [(L Exp2, Ty2)] -> SyM L3.Exp3
          go2 d [] = return $ MkProdE [l$ VarE sloc, l$ VarE d]

          go2 d ((rnd, ty):rst) = do
            d' <- gensym "writecur"
            case ty of
              _ | isPackedTy ty -> do
                 rnd' <- go tenv rnd
                 LetE (d',[], CursorTy, projEnds rnd') <$> l <$>
                   go2 d' rst

              IntTy -> do
                rnd' <- cursorizeExp ddfs fundefs denv tenv rnd
                LetE (d',[], CursorTy, l$ Ext $ L3.WriteInt d rnd') <$> l <$>
                  go2 d' rst

              CursorTy -> do
                rnd' <- cursorizeExp ddfs fundefs denv tenv rnd
                LetE (d',[], CursorTy, l$ Ext $ L3.WriteCursor d rnd') <$> l <$>
                  go2 d' rst
              _ -> error "Unknown type encounterred while cursorizing DataConE."

      writetag <- gensym "writetag"
      dl <$>
        LetE (writetag,[], CursorTy, l$ Ext $ L3.WriteTag dcon sloc) <$> l <$>
          go2 writetag (zip args (lookupDataCon ddfs dcon))

    TimeIt e t b -> do
      Di e' <- go tenv e
      return $ Di $ l$ TimeIt e' (L3.stripTyLocs t) b

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
            _ -> return $ Di $ l$ MkProdE $ L.foldr (\loc acc -> (l$ VarE loc):acc) [fromDi v'] locs

        LetRegionE r bod -> do
          onDi (mkLets (regionToBnds r)) <$> go tenv bod

        FromEndE{} -> error $ "cursorizePackedExp: TODO " ++ sdoc ext

        BoundsCheck i bound cur -> return <$> dl <$> Ext $ L3.BoundsCheck i bound cur

        IndirectionE _ (at,r1) (to,r2) -> do
          onDi (mkLets [("_",[],IntTy, l$ Ext (L3.BumpRefCount (toEndV r1) (toEndV r2)))]) <$>
            go tenv (l$ DataConE at indirectionTag [l$ VarE to])

    MapE{}  -> error $ "TODO: cursorizePackedExp MapE"
    FoldE{} -> error $ "TODO: cursorizePackedExp FoldE"

  where go = cursorizePackedExp ddfs fundefs denv
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
                  _ -> let sizeVar = varAppend "sizeof_" v
                           sizeVal = l$ Ext $ L3.SizeOfScalar v
                           rhs = l$ Ext $ L3.AddCursor loc (l$ VarE (sizeVar))
                       in mkLets [(sizeVar,[], IntTy, sizeVal)] rhs
      if isBound loc
      then Right bod
      else Left $ M.insertWith (++) loc
                  -- TODO: sizeVar is lost here...
                  [(lvar,[],CursorTy,bod)]
                  denv

    FromEndLE loc -> if isBound loc
                     then Right$ l$ VarE loc
                     else Left$ M.insertWith (++) loc [(lvar,[],CursorTy,l$ VarE loc)] denv
    StartOfLE r   -> Right$ case r of
                       GlobR v _ -> l$ VarE v
                       VarR v    -> l$ VarE v
                       DynR v _  -> l$ VarE v
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
cursorizeAppE :: DDefs Ty2 -> NewFuns -> DepEnv -> TEnv -> L Exp2 -> SyM L3.Exp3
cursorizeAppE ddfs fundefs denv tenv (L _ ex) =
  case ex of
    AppE f locs arg -> do
      let fnTy   = case M.lookup f fundefs of
                     Just g -> funty g
                     Nothing -> error $ "Unknown function: " ++ sdoc f
          inT    = arrIn fnTy
          inLocs = inLocVars fnTy
          numRegs = length (outRegVars fnTy) + length (inRegVars fnTy)
          -- Drop input locations, but keep everything else
          outs   = (take numRegs locs) ++  (drop numRegs $ drop (length inLocs) $ locs)
          argTy  = gTypeExp ddfs (Env2 tenv M.empty) arg
      arg' <- if hasPacked inT
              then fromDi <$> cursorizePackedExp ddfs fundefs denv tenv arg
              else cursorizeExp ddfs fundefs denv tenv arg
      starts <- return $ giveStarts argTy arg'
      case locs of
        [] -> return $ AppE f [] starts
        _  -> return $ AppE f [] (l$ MkProdE $ [l$ VarE loc | loc <- outs] ++ [starts])
    _ -> error $ "cursorizeAppE: Unexpected " ++ sdoc ex


{- Note [Cursorizing let expressions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

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
cursorizeLet :: DDefs Ty2 -> NewFuns -> DepEnv -> TEnv -> Bool
             -> (Var, [Var], Ty2, L Exp2) -> L Exp2 -> SyM L3.Exp3
cursorizeLet ddfs fundefs denv tenv isPackedContext (v,locs,ty,rhs) bod
    | isPackedTy ty = do
        rhs' <- fromDi <$> cursorizePackedExp ddfs fundefs denv tenv rhs
        fresh <- gensym "tup_packed"
        let ty' = case locs of
                    [] -> L3.cursorizeTy ty
                    xs -> ProdTy ([CursorTy | _ <- xs] ++ [L3.cursorizeTy ty])

            tenv' = L.foldr (\(a,b) acc -> M.insert a b acc) tenv $
                      [(v, ty),(fresh, ty'),(toEndV v, projTy 1 ty')] ++ [(loc,CursorTy) | loc <- locs]

            -- TEnv and L3 expresssions are tagged with different types
            ty''  = L3.stripTyLocs ty'
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

        bod' <- go tenv' bod
        return $ unLoc $ mkLets bnds bod'

    | forgivingHasPacked ty = do
        rhs' <- fromDi <$> cursorizePackedExp ddfs fundefs denv tenv rhs
        fresh <- gensym "tup_haspacked"
        let ty' = case locs of
                    [] -> L3.cursorizeTy ty
                    xs -> ProdTy ([CursorTy | _ <- xs] ++ [L3.cursorizeTy ty])
            ty''  = L3.stripTyLocs ty'
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
            [] -> LetE (v,[],L3.stripTyLocs ty, rhs') <$>
                    go (M.insert v ty tenv) bod
{-
             This was a scalar binding before, but now has been transformed to
             also return an end_read cursor. So the type of the binding now
             becomes:

                 ProdTy [CursorTy, old_ty]

             Also, the binding itself now changes to:

                 end_read -> ProjE 0 RHS'
                 v        -> ProjE 1 RHS'

             `rightmost` is an example of a program that does this
-}
            [loc] -> do
              fresh <- gensym "tup_scalar"
              let ty'  = ProdTy ([CursorTy | _ <- locs] ++ [L3.cursorizeTy ty])
                  -- We cannot resuse ty' here because TEnv and expresssions are
                  -- tagged with different
                  ty'' = L3.stripTyLocs ty'
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


-- (1) Take a cursor pointing to the start of the tag, and advance it by 1 byte.
-- (2) If the first bound varaible is a scalar (IntTy), read it using the newly
-- returned cursor. Otherwise, just process the body. it'll have the correct
-- instructions to process other bound locations
unpackDataCon :: DDefs Ty2 -> NewFuns -> DepEnv -> TEnv -> Bool -> Var
              -> (DataCon, [(Var, Var)], L Exp2) -> SyM (DataCon, [t], L L3.Exp3)
unpackDataCon ddfs fundefs denv1 tenv isPacked scrtCur (dcon,vlocs,rhs) = do

  let indrVars = if isIndrDataCon dcon
                 then (case numIndrsDataCon ddfs (fromIndrDataCon dcon) of
                         Just n ->
                           let indrs = L.map fst $ take n vlocs
                               vars  = L.map fst $ reverse (take n (reverse vlocs))
                           in zip indrs vars
                         Nothing -> error $ "unpackDataCon: Sized constructor should have packed fields.")
                 else []
  cur <- gensym scrtCur
  (dcon,[],)
    <$> mkLets [(cur,[],CursorTy, l$ Ext $ L3.AddCursor scrtCur (l$ LitE 1))]
    <$> go cur vlocs tys indrVars True denv1 (M.insert cur CursorTy tenv)
  where
        tys  = lookupDataCon ddfs dcon
        processRhs denv env = if isPacked
                              then fromDi <$> cursorizePackedExp ddfs fundefs denv env rhs
                              else cursorizeExp ddfs fundefs denv env rhs

        -- Loop over fields.  Issue reads to get out all Ints. Otherwise, just bind vars to locations
        --
        go :: (Show t) => Var -> [(Var, Var)] -> [UrTy t] -> [(Var, Var)] -> Bool -> DepEnv -> TEnv -> SyM (L L3.Exp3)
        go _c [] [] _ _isFirst denv env = processRhs denv env
        go cur ((v,loc):rst) (ty:rtys) indrVars canBind denv env =
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
                bod <- go (toEndV v) rst rtys indrVars canBind denv env''
                return $ mkLets bnds' bod
              else do
                let denv'' = M.insertWith (++) loc bnds denv
                go (toEndV v) rst rtys indrVars canBind denv'' env'

            _ -> do
              let env' = M.insert v CursorTy env
              case indrVars of
                [] -> do
                  if canBind
                  then do
                    bod <- go (toEndV v) rst rtys indrVars False denv (M.insert loc CursorTy env')
                    return $ mkLets [(loc, [], CursorTy, l$ VarE cur)
                                    ,(v  , [], CursorTy, l$ VarE loc)]
                             bod
                  else do
                    -- Don't create a `let v = loc` binding. Instead, add it to DepEnv
                    let denv'' = M.insertWith (++) loc [(v,[],CursorTy,l$ VarE loc)] denv
                    go (toEndV v) rst rtys indrVars False denv'' env'

                -- Unpacking indirections
                ((_,dep):rest_indrs) -> do
                  tmp1 <- gensym "tmp1"
                  tmp2 <- gensym "tmp2"
                  tagindr <- gensym "tag_indr"
                  ptrindr <- gensym "ptr_indr"

                  let env'' = M.fromList [(tmp1     , ProdTy [IntTy, CursorTy])
                                         ,(tagindr  , IntTy)
                                         ,(ptrindr  , CursorTy)
                                         ,(tmp2     , ProdTy [CursorTy, CursorTy])
                                         ,(v        , CursorTy)
                                         ,(toEndV v , CursorTy)]
                  bod <- go v rst rtys rest_indrs True denv (M.union env' env'')
                  return $
                    mkLets [(loc      , [], CursorTy, l$ VarE cur),
                            (tmp1     , [], ProdTy [IntTy, CursorTy], l$ Ext $ L3.ReadTag loc),
                            (tagindr  , [], IntTy   , l$ ProjE 0 (l$ VarE tmp1)),
                            (ptrindr  , [], CursorTy, l$ ProjE 1 (l$ VarE tmp1)),
                            (tmp2     , [], ProdTy [CursorTy, CursorTy], l$ Ext $ L3.ReadCursor ptrindr),
                            (v        , [], CursorTy, l$ ProjE 0 (l$ VarE tmp2)),
                            (toEndV v , [], CursorTy, l$ ProjE 1 (l$ VarE tmp2)),
                            (dep      , [], CursorTy, l$ VarE v)]
                           bod

        go _ vls rtys _ _ _ _ = error $ "Unexpected numnber of varible, type pairs: " ++ show (vls,rtys)

 -- |
giveStarts :: Ty2 -> L L3.Exp3 -> L L3.Exp3
giveStarts ty e =
  case ty of
    PackedTy{} -> mkProjE 0 e
    ProdTy tys -> case unLoc e of
                    MkProdE es -> l$ MkProdE $ L.map (\(ty',e') -> giveStarts ty' e') (zip tys es)
                    VarE{} -> l$ MkProdE $ L.map (\(ty',n) -> giveStarts ty' (mkProjE n e)) (zip tys [0..])
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


-- | Bindings for a letregion
regionToBnds :: Region -> [(Var, [()], L3.Ty3, L L3.Exp3)]
regionToBnds r =
  case r of
    VarR{} -> error $ "Unexpected VarR in Cursorize." ++ sdoc r
    GlobR v mul -> [ (v       , [], CursorTy, l$ Ext$ L3.NewBuffer mul)
                   , (toEndV v, [], CursorTy, l$ Ext$ L3.AddCursor v (l$ Ext $ L3.InitSizeOfBuffer mul))]
    DynR v mul  -> [ (v       , [], CursorTy, l$ Ext$ L3.ScopedBuffer mul)
                   , (toEndV v, [], CursorTy, l$ Ext$ L3.AddCursor v (l$ Ext $ L3.InitSizeOfBuffer mul))]

toEndV :: Var -> Var
toEndV = varAppend "end_"

-- | A lenient version of L1.hasPacked which doesn't throw an error if it sees a CursorTy
forgivingHasPacked :: Show a => UrTy a -> Bool
forgivingHasPacked t =
  case t of
    PackedTy{}     -> True
    ProdTy ls      -> any forgivingHasPacked ls
    SymTy          -> False
    BoolTy         -> False
    IntTy          -> False
    SymDictTy ty   -> forgivingHasPacked ty
    ListTy _       -> error "FINISHLISTS"
    CursorTy       -> False
    PtrTy          -> False

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
