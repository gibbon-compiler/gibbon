{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Gibbon.Language
    ( module Gibbon.Language.Constants
    , module Gibbon.Language.Syntax

      -- * Helpers operating on expressions
    , mapExt, mapLocs, mapExprs, mapMExprs, visitExp
    , subst, substE, hasTimeIt, hasSpawns, hasSpawnsProg, projNonFirst
    , mkProj, mkProd, mkLets, flatLets, tuplizeRefs

      -- * Helpers operating on types
    , mkProdTy, projTy , voidTy, isProdTy, isNestedProdTy, isPackedTy, isScalarTy
    , hasPacked, sizeOfTy, primArgsTy, primRetTy, tyToDataCon
    , stripTyLocs, isValidListElemTy, getPackedTys

      -- * Misc
    , assertTriv, assertTrivs

    ) where

import qualified Data.Map as M
import           Data.List as L
import qualified Data.Set as S
-- import           Data.Functor.Foldable
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Language.Constants
import           Gibbon.Language.Syntax
import           Gibbon.Common

--------------------------------------------------------------------------------

instance (Out l, Show l, Show d, Out d, Expression (e l d))
      => Expression (PreExp e l d) where
  type (TyOf (PreExp e l d))  = d
  type (LocOf (PreExp e l d)) = l
  isTrivial = f
    where
      f :: (PreExp e l d) -> Bool
      f e =
       case e of
        VarE _     -> True
        LitE _     -> True
        FloatE{}   -> True
        LitSymE _  -> True
        PrimAppE{} -> False

        ----------------- POLICY DECISION ---------------
        -- Tuples and projections are NOT trivial!
        ProjE{}    -> False
        MkProdE{}  -> False

        -- DataCon's are a bit tricky.  May want to inline them at
        -- some point if it avoids region conflicts.
        DataConE{} -> False

        IfE{}      -> False
        CaseE{}    -> False
        LetE {}    -> False
        MapE {}    -> False
        FoldE {}   -> False
        AppE  {}   -> False
        TimeIt {}  -> False
        WithArenaE{} -> False
        SpawnE{}   -> False
        SyncE      -> False
        Ext ext -> isTrivial ext

-- | Free data variables.  Does not include function variables, which
-- currently occupy a different namespace.  Does not include location/region variables.
instance FreeVars (e l d) => FreeVars (PreExp e l d) where
  gFreeVars ex = case ex of
      VarE v    -> S.singleton v
      LitE _    -> S.empty
      FloatE{}  -> S.empty
      LitSymE _ -> S.empty
      ProjE _ e -> gFreeVars e
      IfE a b c -> gFreeVars a `S.union` gFreeVars b `S.union` gFreeVars c
      AppE v _ ls         -> S.unions $ (S.singleton v) : (L.map gFreeVars ls)
      PrimAppE _ ls        -> S.unions (L.map gFreeVars ls)
      LetE (v,_,_,rhs) bod -> gFreeVars rhs `S.union`
                              S.delete v (gFreeVars bod)
      CaseE e ls -> S.union (gFreeVars e)
                    (S.unions $ L.map (\(_, vlocs, ee) ->
                                           let (vars,_) = unzip vlocs
                                           in (gFreeVars ee) `S.difference` (S.fromList vars))
                                ls)
      MkProdE ls          -> S.unions $ L.map gFreeVars ls
      DataConE _ _ ls     -> S.unions $ L.map gFreeVars ls
      TimeIt e _ _        -> gFreeVars e
      MapE (v,_t,rhs) bod -> gFreeVars rhs `S.union`
                             S.delete v (gFreeVars bod)
      FoldE (v1,_t1,r1) (v2,_t2,r2) bod ->
          gFreeVars r1 `S.union` gFreeVars r2 `S.union`
          (S.delete v1 $ S.delete v2 $ gFreeVars bod)

      WithArenaE v e -> S.delete v $ gFreeVars e

      SpawnE v _ ls -> S.unions $ (S.singleton v) : (L.map gFreeVars ls)
      SyncE -> S.empty

      Ext q -> gFreeVars q


-- | A Typeable instance for L1 and L3 (L2 defines it's own)
instance (Show (), Out (), Expression (e () (UrTy ())),
          TyOf (e () (UrTy ())) ~ TyOf (PreExp e () (UrTy ())),
          FunctionTy (UrTy ()), Typeable (e () (UrTy ())))
       => Typeable (PreExp e () (UrTy ())) where
  gRecoverType ddfs env2 ex =
    case ex of
      VarE v       -> M.findWithDefault (error $ "Cannot find type of variable " ++ show v ++ " in " ++ show (vEnv env2)) v (vEnv env2)
      LitE _       -> IntTy
      FloatE{}     -> FloatTy
      LitSymE _    -> SymTy
      AppE v _ _   -> outTy $ fEnv env2 # v
      PrimAppE (DictInsertP ty) ((VarE v):_) -> SymDictTy (Just v) $ stripTyLocs ty
      PrimAppE (DictEmptyP  ty) ((VarE v):_) -> SymDictTy (Just v) $ stripTyLocs ty
      PrimAppE p _ -> primRetTy p

      LetE (v,_,t,_) e -> gRecoverType ddfs (extendVEnv v t env2) e
      IfE _ e _        -> gRecoverType ddfs env2 e
      MkProdE es       -> ProdTy $ L.map (gRecoverType ddfs env2) es
      DataConE loc c _ -> PackedTy (getTyOfDataCon ddfs c) loc
      TimeIt e _ _     -> gRecoverType ddfs env2 e
      MapE _ e         -> gRecoverType ddfs env2 e
      FoldE _ _ e      -> gRecoverType ddfs env2 e
      Ext ext          -> gRecoverType ddfs env2 ext
      ProjE i e ->
        case gRecoverType ddfs env2 e of
          (ProdTy tys) -> tys !! i
          oth -> error$ "typeExp: Cannot project fields from this type: "++show oth
                        ++"\nExpression:\n  "++ sdoc ex
                        ++"\nEnvironment:\n  "++sdoc (vEnv env2)
      WithArenaE _v e -> gRecoverType ddfs env2 e
      SpawnE v _ _    -> outTy $ fEnv env2 # v
      SyncE           -> voidTy
      CaseE _ mp ->
        let (c,args,e) = head mp
            args' = L.map fst args
        in gRecoverType ddfs (extendsVEnv (M.fromList (zip args' (lookupDataCon ddfs c))) env2) e


instance Renamable Var where
  gRename env v = M.findWithDefault v v env

instance HasSubstitutable e l d => Substitutable (PreExp e l d) where
  gSubst  = subst
  gSubstE = substE

instance HasRenamable e l d => Renamable (PreExp e l d) where
  gRename env ex =
    case ex of
      VarE v -> VarE (go v)
      LitE{}    -> ex
      FloatE{}  -> ex
      LitSymE{} -> ex
      AppE f locs args -> AppE (go f) (gol locs) (gol args)
      PrimAppE pr args -> PrimAppE pr (gol args)
      LetE (v,locs,ty,rhs) bod -> LetE (go v, gol locs, go ty, go rhs) (go bod)
      IfE a b c  -> IfE (go a) (go b) (go c)
      MkProdE ls -> MkProdE (gol ls)
      ProjE i e  -> ProjE i (go e)
      CaseE scrt ls ->
        CaseE (go scrt) (map (\(a,b,c) -> (a, map (\(d,e) -> (go d, go e)) b, go c)) ls)
      DataConE loc dcon ls -> DataConE (go loc) dcon (gol ls)
      TimeIt e ty b -> TimeIt (go e) (go ty) b
      SpawnE f locs args -> SpawnE (go f) (gol locs) (gol args)
      SyncE   -> SyncE
      WithArenaE v e -> WithArenaE (go v) (go e)
      Ext ext -> Ext (go ext)
      MapE{}  -> ex
      FoldE{} -> ex
     where
       go :: forall a. Renamable a => a -> a
       go = gRename env

       gol :: forall a. Renamable a => [a] -> [a]
       gol ls = map go ls

instance Renamable a => Renamable (UrTy a) where
  gRename env = fmap (gRename env)


--------------------------------------------------------------------------------
-- Helpers operating on expressions
--------------------------------------------------------------------------------

-- | Apply a function to the extension points only.
mapExt :: (e1 l d -> e2 l d) -> PreExp e1 l d -> PreExp e2 l d
mapExt fn = visitExp id fn id

-- | Apply a function to the locations only.
mapLocs :: (e l2 d -> e l2 d) -> PreExp e l2 d -> PreExp e l2 d
mapLocs fn = visitExp id fn id

-- | Transform the expressions within a program.
mapExprs :: (e -> e) -> Prog e -> Prog e
mapExprs fn prg@Prog{fundefs,mainExp} =
  let mainExp' = case mainExp of
                   Nothing -> Nothing
                   Just (ex,ty) -> Just (fn ex, ty)
  in
  prg{ fundefs = M.map (\g -> g {funBody = fn (funBody g)}) fundefs
     , mainExp =  mainExp' }

-- | Monadic 'mapExprs'.
mapMExprs :: Monad m => (e -> m e) -> Prog e -> m (Prog e)
mapMExprs fn prg@Prog{fundefs,mainExp} = do
  mainExp' <- case mainExp of
                Nothing -> pure Nothing
                Just (ex,ty) -> do ex' <- fn ex
                                   pure $ Just (ex', ty)
  fundefs' <- traverse (\g -> do funBody' <- fn (funBody g)
                                 pure $ g {funBody = funBody'})
                       fundefs
  pure $ prg { fundefs = fundefs', mainExp = mainExp' }


-- | Apply a function to the locations, extensions, and
-- binder-decorations, respectively.
visitExp :: forall l1 l2 e1 e2 d1 d2 .
            (l1 -> l2) -> (e1 l1 d1 -> e2 l2 d2) -> (d1 -> d2) ->
            PreExp e1 l1 d1 -> PreExp e2 l2  d2
visitExp _fl fe _fd exp0 = go exp0
 where
   go :: (PreExp e1 l1  d1) -> (PreExp e2 l2 d2)
   go ex =
     case ex of
       Ext  x  -> Ext (fe x)
       _       -> _finishme


-- | Substitute an expression in place of a variable.
subst :: HasSubstitutable e l d
      => Var -> (PreExp e l d) -> (PreExp e l d) -> (PreExp e l d)
subst old new ex =
  let go = subst old new in
  case ex of
    VarE v | v == old  -> new
           | otherwise -> VarE v
    LitE _             -> ex
    FloatE{}           -> ex
    LitSymE _          -> ex
    AppE v loc ls      -> AppE v loc (map go ls)
    PrimAppE p ls      -> PrimAppE p $ L.map go ls
    LetE (v,loc,t,rhs) bod | v == old  -> LetE (v,loc,t,go rhs) bod
                           | otherwise -> LetE (v,loc,t,go rhs) (go bod)
    ProjE i e  -> ProjE i (go e)
    CaseE e ls ->
                  CaseE (go e) (L.map f ls)
                      where f (c,vs,er) = if L.elem old (L.map fst vs)
                                          then (c,vs,er)
                                          else (c,vs,go er)
    MkProdE ls        -> MkProdE $ L.map go ls
    DataConE loc k ls -> DataConE loc k $ L.map go ls
    TimeIt e t b      -> TimeIt (go e) t b
    IfE a b c         -> IfE (go a) (go b) (go c)

    SpawnE v loc ls   -> SpawnE v loc (map go ls)
    SyncE             -> SyncE

    MapE (v,t,rhs) bod | v == old  -> MapE (v,t, rhs)    (go bod)
                       | otherwise -> MapE (v,t, go rhs) (go bod)
    FoldE (v1,t1,r1) (v2,t2,r2) bod ->
        let r1' = if v1 == old then r1 else go r1
            r2' = if v2 == old then r2 else go r2
        in FoldE (v1,t1,r1') (v2,t2,r2') (go bod)

    Ext ext -> Ext (gSubstExt old new ext)

    WithArenaE v e | v == old  -> WithArenaE v e
                   | otherwise -> WithArenaE v (go e)


-- | Expensive 'subst' that looks for a whole matching sub-EXPRESSION.
-- If the old expression is a variable, this still avoids going under binder.
substE :: HasSubstitutable e l d
       => (PreExp e l d) -> (PreExp e l d) -> (PreExp e l d) -> (PreExp e l d)
substE old new ex =
  let go = substE old new in
  case ex of
    _ | ex == old   -> new

    VarE v          -> VarE v
    LitE _          -> ex
    FloatE{}        -> ex
    LitSymE _       -> ex
    AppE v loc ls   -> AppE v loc (map go ls)
    PrimAppE p ls   -> PrimAppE p $ L.map go ls
    LetE (v,loc,t,rhs) bod | (VarE v) == old  -> LetE (v,loc,t,go rhs) bod
                           | otherwise -> LetE (v,loc,t,go rhs) (go bod)

    ProjE i e         -> ProjE i (go e)
    CaseE e ls        -> CaseE (go e) (L.map (\(c,vs,er) -> (c,vs,go er)) ls)
    MkProdE ls        -> MkProdE $ L.map go ls
    DataConE loc k ls -> DataConE loc k $ L.map go ls
    TimeIt e t b      -> TimeIt (go e) t b
    IfE a b c         -> IfE (go a) (go b) (go c)
    SpawnE v loc ls   -> SpawnE v loc (map go ls)
    SyncE             -> SyncE
    MapE (v,t,rhs) bod | VarE v == old  -> MapE (v,t, rhs)    (go bod)
                       | otherwise -> MapE (v,t, go rhs) (go bod)
    FoldE (v1,t1,r1) (v2,t2,r2) bod ->
        let r1' = if VarE v1 == old then r1 else go r1
            r2' = if VarE v2 == old then r2 else go r2
        in FoldE (v1,t1,r1') (v2,t2,r2') (go bod)

    Ext ext -> Ext (gSubstEExt old new ext)

    WithArenaE v e | (VarE v) == old -> WithArenaE v e
                   | otherwise -> WithArenaE v (go e)


-- | Does the expression contain a TimeIt form?
hasTimeIt :: (PreExp e l d) -> Bool
hasTimeIt rhs =
    case rhs of
      TimeIt _ _ _ -> True
      DataConE{}   -> False
      VarE _       -> False
      LitE _       -> False
      FloatE{}     -> False
      LitSymE _    -> False
      AppE _ _ _   -> False
      PrimAppE _ _ -> False
      ProjE _ e    -> hasTimeIt e
      MkProdE ls   -> any hasTimeIt ls
      IfE a b c    -> hasTimeIt a || hasTimeIt b || hasTimeIt c
      CaseE _ ls   -> any hasTimeIt [ e | (_,_,e) <- ls ]
      LetE (_,_,_,e1) e2 -> hasTimeIt e1 || hasTimeIt e2
      SpawnE _ _ _       -> False
      SyncE              -> False
      MapE (_,_,e1) e2   -> hasTimeIt e1 || hasTimeIt e2
      FoldE (_,_,e1) (_,_,e2) e3 -> hasTimeIt e1 || hasTimeIt e2 || hasTimeIt e3
      Ext _ -> False
      WithArenaE _ e -> hasTimeIt e

hasSpawnsProg :: Prog (PreExp e l d) -> Bool
hasSpawnsProg (Prog _ fundefs mainExp) =
  any (\FunDef{funBody} -> hasSpawns funBody) (M.elems fundefs) ||
    case mainExp of
      Nothing      -> False
      Just (e,_ty) -> hasSpawns e

-- | Does the expression contain a SpawnE form?
hasSpawns :: (PreExp e l d) -> Bool
hasSpawns rhs =
    case rhs of
      DataConE{}   -> False
      VarE{}       -> False
      LitE{}       -> False
      FloatE{}     -> False
      LitSymE{}    -> False
      AppE{}       -> False
      PrimAppE{}   -> False
      ProjE _ e    -> hasSpawns e
      MkProdE ls   -> any hasSpawns ls
      IfE a b c    -> hasSpawns a || hasSpawns b || hasSpawns c
      CaseE _ ls   -> any hasSpawns [ e | (_,_,e) <- ls ]
      LetE (_,_,_,e1) e2 -> hasSpawns e1 || hasSpawns e2
      SpawnE{}     -> True
      SyncE        -> False
      TimeIt e _ _ -> hasSpawns e
      MapE (_,_,e1) e2   -> hasSpawns e1 || hasSpawns e2
      FoldE (_,_,e1) (_,_,e2) e3 ->
        hasSpawns e1 || hasSpawns e2 || hasSpawns e3
      Ext _ -> False
      WithArenaE _ e -> hasSpawns e

-- | Project something which had better not be the first thing in a tuple.
projNonFirst :: (Out l, Out d, Out (e l d)) => Int -> (PreExp e l d) -> (PreExp e l d)
projNonFirst 0 e = error $ "projNonFirst: expected nonzero index into expr: " ++ sdoc e
projNonFirst i e = ProjE i e

-- | Smart constructor that immediately destroys products if it can:
-- Does NOT avoid single-element tuples.
mkProj :: Int -> (PreExp e l d) -> (PreExp e l d)
mkProj ix (MkProdE ls) = ls !! ix
mkProj ix e = (ProjE ix e)

-- | Make a product type while avoiding unary products.
mkProd :: [(PreExp e l d)]-> (PreExp e l d)
mkProd [e] = e
mkProd ls  = MkProdE ls

-- | Make a nested series of lets.
mkLets :: [(Var, [loc], dec, (PreExp ext loc dec))] -> (PreExp ext loc dec) -> (PreExp ext loc dec)
mkLets [] bod     = bod
mkLets (b:bs) bod = LetE b (mkLets bs bod)

-- | Helper function that lifts out Lets on the RHS of other Lets.
-- Absolutely requires unique names.
mkLetE :: (Var, [l], d, (PreExp e l d)) -> (PreExp e l d) -> (PreExp e l d)
mkLetE (vr,lvs,ty,(LetE bnd e)) bod = mkLetE bnd $ mkLetE (vr,lvs,ty,e) bod
mkLetE bnd bod = LetE bnd bod

-- | Alternative version of L1.mkLets that also flattens
flatLets :: [(Var,[l],d,(PreExp e l d))] -> (PreExp e l d) -> (PreExp e l d)
flatLets [] bod = bod
flatLets (b:bs) bod = mkLetE b (flatLets bs bod)

tuplizeRefs :: Var -> [Var] -> [d] -> (PreExp e l d) -> (PreExp e l d)
tuplizeRefs ref vars tys =
  mkLets $
    L.map (\(v,ty,ix) -> (v,[],ty,mkProj ix (VarE ref))) (L.zip3 vars tys [0..])

--------------------------------------------------------------------------------
-- Helpers operating on types
--------------------------------------------------------------------------------

-- | Same as mkProd, at the type level
mkProdTy :: [UrTy a]-> UrTy a
mkProdTy [t] = t
mkProdTy ls  = ProdTy ls

projTy :: (Out a) => Int -> UrTy a -> UrTy a
projTy 0 (ProdTy (ty:_))  = ty
projTy n (ProdTy (_:tys)) = projTy (n-1) (ProdTy tys)
projTy _ ty = error $ "projTy: " ++ sdoc ty ++ " is not a projection!"

-- | A makeshift void type.
voidTy :: UrTy a
voidTy = ProdTy []

-- | Are values of this type tuples ?
isProdTy :: UrTy a -> Bool
isProdTy ProdTy{} = True
isProdTy _ = False

-- | Do values of this type contain nested tuples ?
isNestedProdTy :: UrTy a -> Bool
isNestedProdTy ty =
  case ty of
    ProdTy tys -> if any isProdTy tys
                  then True
                  else False
    _ -> False

-- | Are values of this type Packed ?
isPackedTy :: UrTy a -> Bool
isPackedTy PackedTy{} = True
isPackedTy _ = False

isScalarTy :: UrTy a -> Bool
isScalarTy IntTy  = True
isScalarTy SymTy  = True
isScalarTy BoolTy = True
isScalarTy FloatTy= True
isScalarTy _      = False

-- | Lists of scalars or flat products of scalars are allowed.
isValidListElemTy :: UrTy a -> Bool
isValidListElemTy ty
  | isScalarTy ty = True
  | otherwise = case ty of
                  VectorTy elty -> isValidListElemTy elty
                  ProdTy tys    -> all isScalarTy tys
                  _ -> False

-- | Do values of this type contain packed data?
hasPacked :: Show a => UrTy a -> Bool
hasPacked t =
  case t of
    PackedTy{}     -> True
    ProdTy ls      -> any hasPacked ls
    SymTy          -> False
    BoolTy         -> False
    IntTy          -> False
    FloatTy        -> False
    SymDictTy _ _  -> False -- hasPacked ty
    PDictTy k v    -> hasPacked k || hasPacked v
    VectorTy ty    -> hasPacked ty
    ListTy ty      -> hasPacked ty
    PtrTy          -> False
    CursorTy       -> False
    ArenaTy        -> False
    SymSetTy       -> False
    SymHashTy      -> False
    IntHashTy      -> False


-- | Get all packed types in a type.
getPackedTys :: Show a => UrTy a -> [UrTy a]
getPackedTys t =
  case t of
    PackedTy{}     -> [t]
    ProdTy ls      -> concatMap getPackedTys ls
    SymTy          -> []
    BoolTy         -> []
    IntTy          -> []
    FloatTy        -> []
    SymDictTy _ _  -> [] -- getPackedTys ty
    PDictTy k v    -> getPackedTys k ++ getPackedTys v
    VectorTy ty    -> getPackedTys ty
    ListTy ty      -> getPackedTys ty
    PtrTy          -> []
    CursorTy       -> []
    ArenaTy        -> []
    SymSetTy       -> []
    SymHashTy      -> []
    IntHashTy      -> []

-- | Provide a size in bytes, if it is statically known.
sizeOfTy :: UrTy a -> Maybe Int
sizeOfTy t =
  case t of
    PackedTy{}    -> Nothing
    ProdTy ls     -> sum <$> mapM sizeOfTy ls
    SymDictTy _ _ -> Just 8 -- Always a pointer.
    PDictTy _ _   -> Just 8 -- Always a pointer.
    IntTy         -> Just 8
    FloatTy       -> Just 4
    SymTy         -> Just 8
    BoolTy        -> Just 1
    VectorTy{}    -> Just 8 -- Always a pointer.
    ListTy{}      -> Just 8 -- Always a pointer.
    PtrTy{}       -> Just 8 -- Assuming 64 bit
    CursorTy{}    -> Just 8
    ArenaTy       -> Just 8
    SymSetTy      -> error "sizeOfTy: SymSetTy not handled."
    SymHashTy     -> error "sizeOfTy: SymHashTy not handled."
    IntHashTy     -> error "sizeOfTy: SymHashTy not handled."

-- | Type of the arguments for a primitive operation.
primArgsTy :: Prim (UrTy a) -> [UrTy a]
primArgsTy p =
  case p of
    AddP    -> [IntTy, IntTy]
    SubP    -> [IntTy, IntTy]
    MulP    -> [IntTy, IntTy]
    DivP    -> [IntTy, IntTy]
    ModP    -> [IntTy, IntTy]
    ExpP    -> [IntTy, IntTy]
    FRandP  -> []
    FAddP   -> [FloatTy, FloatTy]
    FSubP   -> [FloatTy, FloatTy]
    FMulP   -> [FloatTy, FloatTy]
    FDivP   -> [FloatTy, FloatTy]
    FExpP   -> [FloatTy, FloatTy]
    FSqrtP  -> [FloatTy]
    FTanP   -> [FloatTy]
    FloatToIntP -> [FloatTy]
    IntToFloatP -> [IntTy]
    RandP   -> []
    EqSymP  -> [SymTy, SymTy]
    EqIntP  -> [IntTy, IntTy]
    EqFloatP-> [FloatTy, FloatTy]
    LtP  -> [IntTy, IntTy]
    GtP  -> [IntTy, IntTy]
    LtEqP-> [IntTy, IntTy]
    GtEqP-> [IntTy, IntTy]
    FLtP  -> [FloatTy, FloatTy]
    FGtP  -> [FloatTy, FloatTy]
    FLtEqP-> [FloatTy, FloatTy]
    FGtEqP-> [FloatTy, FloatTy]
    OrP  -> [BoolTy, BoolTy]
    AndP -> [BoolTy, BoolTy]
    Gensym  -> []
    MkTrue  -> []
    MkFalse -> []
    SizeParam        -> []
    BenchProgParam   -> []
    IsBig            -> [IntTy, PackedTy "HOLE" _error]
    DictEmptyP _ty   -> []
    DictInsertP _ty  -> error "primArgsTy: dicts not handled yet"
    DictLookupP _ty  -> error "primArgsTy: dicts not handled yet"
    DictHasKeyP _ty  -> error "primArgsTy: dicts not handled yet"
    VAllocP _elty  -> [IntTy]
    VFreeP elty   -> [VectorTy elty]
    VFree2P elty  -> [VectorTy elty]
    VLengthP elty -> [VectorTy elty]
    VNthP elty    -> [VectorTy elty, IntTy]
    VSliceP elty  -> [IntTy, IntTy, VectorTy elty]
    InplaceVUpdateP elty -> [VectorTy elty, IntTy, elty]
    VConcatP elty -> [VectorTy (VectorTy elty)]
    -- The voidTy is just a placeholder.
    -- We don't have a type for function pointers.
    VSortP elty        -> [VectorTy elty, voidTy]
    InplaceVSortP elty -> [VectorTy elty, voidTy]
    PDictInsertP kty vty -> [kty, vty, PDictTy kty vty]
    PDictLookupP kty vty -> [kty, PDictTy kty vty]
    PDictAllocP _kty _vty -> []
    PDictHasKeyP kty vty -> [kty, PDictTy kty vty]
    PDictForkP kty vty -> [PDictTy kty vty]
    PDictJoinP kty vty -> [PDictTy kty vty, PDictTy kty vty]
    LLAllocP _elty -> []
    LLIsEmptyP elty -> [ListTy elty]
    LLConsP elty  -> [elty, ListTy elty]
    LLHeadP elty  -> [ListTy elty]
    LLTailP elty  -> [ListTy elty]
    LLFreeP elty   -> [ListTy elty]
    LLFree2P elty  -> [ListTy elty]
    LLCopyP elty  -> [ListTy elty]
    GetNumProcessors -> []
    PrintInt -> [IntTy]
    PrintFloat -> [FloatTy]
    PrintBool -> [BoolTy]
    PrintSym -> [SymTy]
    ReadInt  -> []
    SymSetEmpty -> []
    SymSetInsert -> [SymSetTy, SymTy]
    SymSetContains -> [SymSetTy, SymTy]
    SymHashEmpty -> []
    SymHashInsert -> [SymHashTy,SymTy,SymTy]
    SymHashLookup -> [SymHashTy,SymTy]
    SymHashContains -> [SymHashTy,SymTy]
    IntHashEmpty -> []
    IntHashInsert -> [IntHashTy,SymTy,IntTy]
    IntHashLookup -> [IntHashTy,SymTy]
    ReadPackedFile{} -> []
    ReadArrayFile{}  -> []
    (ErrorP _ _) -> []
    RequestEndOf  -> error "primArgsTy: RequestEndOf not handled yet"
    RequestSizeOf -> error "primArgsTy: RequestSizeOf not handled yet"
    WritePackedFile{} -> error "primArgsTy: WritePackedFile not handled yet"
    Write3dPpmFile{} -> error "primArgsTy: Write3dPpmFile not handled yet"

-- | Return type for a primitive operation.
primRetTy :: Prim (UrTy a) -> (UrTy a)
primRetTy p =
  case p of
    AddP -> IntTy
    SubP -> IntTy
    MulP -> IntTy
    DivP -> IntTy
    ModP -> IntTy
    ExpP -> IntTy
    FRandP-> FloatTy
    FAddP -> FloatTy
    FSubP -> FloatTy
    FMulP -> FloatTy
    FDivP -> FloatTy
    FExpP -> FloatTy
    FSqrtP-> FloatTy
    FTanP -> FloatTy
    FloatToIntP -> IntTy
    IntToFloatP -> FloatTy
    RandP-> IntTy
    Gensym  -> SymTy
    EqSymP  -> BoolTy
    EqIntP  -> BoolTy
    EqFloatP-> BoolTy
    LtP  -> BoolTy
    GtP  -> BoolTy
    LtEqP-> BoolTy
    GtEqP-> BoolTy
    FLtP  -> BoolTy
    FGtP  -> BoolTy
    FLtEqP-> BoolTy
    FGtEqP-> BoolTy
    OrP  -> BoolTy
    AndP -> BoolTy
    MkTrue  -> BoolTy
    MkFalse -> BoolTy
    SizeParam      -> IntTy
    BenchProgParam -> SymTy
    IsBig          -> BoolTy
    DictHasKeyP _  -> BoolTy
    DictEmptyP ty  -> SymDictTy Nothing $ stripTyLocs ty
    DictInsertP ty -> SymDictTy Nothing $ stripTyLocs ty
    DictLookupP ty -> ty
    VAllocP elty   -> VectorTy elty
    VFreeP _elty   -> ProdTy []
    VFree2P _elty  -> ProdTy []
    VLengthP _elty -> IntTy
    VNthP elty     -> elty
    VSliceP elty   -> VectorTy elty
    InplaceVUpdateP elty -> VectorTy elty
    VConcatP elty  -> VectorTy elty
    VSortP elty -> VectorTy elty
    InplaceVSortP elty -> VectorTy elty
    PDictInsertP kty vty -> PDictTy kty vty
    PDictLookupP _kty vty -> vty
    PDictAllocP kty vty -> PDictTy kty vty
    PDictHasKeyP _kty _vty -> BoolTy
    PDictForkP kty vty -> ProdTy [PDictTy kty vty, PDictTy kty vty]
    PDictJoinP kty vty -> PDictTy kty vty
    LLAllocP elty -> ListTy elty
    LLIsEmptyP _elty -> BoolTy
    LLConsP elty  -> ListTy elty
    LLHeadP elty  -> elty
    LLTailP elty  -> ListTy elty
    LLFreeP _elty  -> ProdTy []
    LLFree2P _elty -> ProdTy []
    LLCopyP elty  -> ListTy elty
    GetNumProcessors -> IntTy
    PrintInt   -> ProdTy []
    PrintFloat -> ProdTy []
    PrintBool  -> ProdTy []
    PrintSym   -> ProdTy []
    ReadInt    -> IntTy
    SymSetEmpty    -> SymSetTy
    SymSetInsert   -> SymSetTy
    SymSetContains -> BoolTy
    SymHashEmpty   -> SymHashTy
    SymHashInsert  -> SymHashTy
    SymHashLookup  -> SymTy
    SymHashContains  -> BoolTy
    IntHashEmpty   -> IntHashTy
    IntHashInsert  -> IntHashTy
    IntHashLookup  -> IntTy
    (ErrorP _ ty)  -> ty
    ReadPackedFile _ _ _ ty -> ty
    ReadArrayFile _ ty      -> ty
    RequestEndOf  -> CursorTy
    RequestSizeOf -> IntTy
    WritePackedFile{} -> error "primRetTy: WritePackedFile not handled yet"
    Write3dPpmFile{} -> error "primRetTy: Write3dPpmFile not handled yet"

stripTyLocs :: UrTy a -> UrTy ()
stripTyLocs ty =
  case ty of
    IntTy     -> IntTy
    FloatTy   -> FloatTy
    SymTy     -> SymTy
    BoolTy    -> BoolTy
    ProdTy ls -> ProdTy $ L.map stripTyLocs ls
    SymDictTy v ty'  -> SymDictTy v $ stripTyLocs ty'
    PDictTy k v -> PDictTy (stripTyLocs k) (stripTyLocs v)
    PackedTy tycon _ -> PackedTy tycon ()
    VectorTy ty' -> VectorTy $ stripTyLocs ty'
    ListTy ty' -> ListTy $ stripTyLocs ty'
    PtrTy    -> PtrTy
    CursorTy -> CursorTy
    SymSetTy -> SymSetTy
    SymHashTy -> SymHashTy
    IntHashTy -> IntHashTy
    ArenaTy   -> ArenaTy

-- | Get the data constructor type from a type, failing if it's not packed
tyToDataCon :: Show a => UrTy a -> DataCon
tyToDataCon (PackedTy dcon _) = dcon
tyToDataCon oth = error $ "tyToDataCon: " ++ show oth ++ " is not packed"

-- | Ensure that an expression is trivial.
assertTriv :: (Expression e) => e -> a -> a
assertTriv e =
  if isTrivial e
  then id
  else error$ "Expected trivial argument, got: "++sdoc e

-- | List version of 'assertTriv'.
assertTrivs :: (Expression e) => [e] -> a -> a
assertTrivs [] = id
assertTrivs (a:b) = assertTriv a . assertTrivs b
