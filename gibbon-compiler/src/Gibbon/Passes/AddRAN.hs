{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Gibbon.Passes.AddRAN
  (addRAN, numRANsDataCon, needsRAN) where

import           Control.Monad ( when, forM )
import           Data.Foldable
import           Data.List as L
import qualified Data.Map as M
import           Data.Maybe ( fromJust )
import qualified Data.Set as S
import           Text.PrettyPrint.GenericPretty

import           Gibbon.Common
import           Gibbon.DynFlags
import           Gibbon.Passes.AddTraversals ( needsTraversalCase )
import           Gibbon.L1.Syntax as L1
import           Gibbon.L2.Syntax

{-

Adding random access nodes
~~~~~~~~~~~~~~~~~~~~~~~~~~

We cannot add RAN's to an L2 program, as it would distort the locations
inferred by the previous analysis. Instead, (1) we use the old L1 program and
add RAN's to that, (2) then run location inference again.

Adding RAN's requires 3 steps:

(1) Convert DDefs to `WithRAN DDefs` (we don't have a separate type for those yet).

For example,

    ddtree :: DDefs Ty1
    ddtree = fromListDD [DDef (toVar "Tree")
                          [ ("Leaf",[(False,IntTy)])
                          , ("Node",[ (False,PackedTy "Tree" ())
                                    , (False,PackedTy "Tree" ())])
                          ]]

becomes,

    ddtree :: DDefs Ty1
    ddtree = fromListDD [DDef (toVar "Tree")
                         [ ("Leaf"   ,[(False,IntTy)])
                         , ("Node",  [ (False,PackedTy "Tree" ())
                                     , (False,PackedTy "Tree" ())])
                         , ("Node^", [ (False, CursorTy) -- random access node
                                     , (False,PackedTy "Tree" ())
                                     , (False,PackedTy "Tree" ())])
                         ]]

(2) Update all data constructors that now need to write additional random access nodes
    (before all other arguments so that they're written immediately after the tag).

(3) Case expressions are modified to work with these updated data constructors.
    Pattern matches for these constructors now bind the additional
    random access nodes too.


Reusing RAN's in case expressions
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

If a data constructor occurs inside a pattern match, we probably already have a
random access node for it. In that case, we don't want to request yet another
one using RequestEndOf. We track this using RANEnv Consider this example:

    (fn ...
      (case tr
        [(Node^ [(ran_y, _) (x, _), (y, _)]
           (DataConE __HOLE x (fn y)))]))

Here, we don't want to fill the HOLE with (RequestEndOf x). Instead, we should reuse ran_y.


When does a type 'needsRAN'
~~~~~~~~~~~~~~~~~~~~~~~~~~~

If any pattern 'needsTraversalCase' to be able to unpack it, we mark the type of
scrutinee as something that needs RAN's. Also, types of all packed values flowing
into a SpawnE that live in the same region would need random access.


Keeping old case clauses around
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Consider this example datatype.

    data Foo = A Foo Foo | B

Suppose that we want to add random access nodes to Foo. Before [2019.09.15],
step (3) above was a destructive operation. Specifically, addRAN would update
a pattern match on 'A' in place.

    case foo of
      A x y -> ...

would become

    case foo of
      A^ ran x y -> ...


As described in this [Evernote], we'd like to amortize the cost of adding
random access nodes to a datatype i.e below a certain threshold, we'd rather
perform dummy traversals. It's clear that if we want to support this, we
cannot get rid of the old case clause. After [2019.09.15], that's what
addRAN does. And we run addTraversals later in the pipeline so that the
case clause is compilable.

Evernote: https://www.evernote.com/l/AF-jUPTw2lZDS440RgWbgj9RMNkttTaKd3Y

-}

--------------------------------------------------------------------------------

-- See [Reusing RAN's in case expressions]
type RANEnv = M.Map Var Var

-- | Operates on an L1 program, and updates it to have random access nodes.
--
-- Previous analysis determines which data types require it (needsLRAN).
addRAN :: S.Set TyCon -> Prog1 -> PassM Prog1
addRAN needRANsTyCons prg@Prog{ddefs,fundefs,mainExp} = do
  dump_op <- dopt Opt_D_Dump_Repair <$> getDynFlags
  when dump_op $
    dbgTrace 2 ("Adding random access nodes: " ++ sdoc (S.toList needRANsTyCons)) (return ())
  let iddefs = withRANDDefs needRANsTyCons ddefs
  funs <- mapM (\(nm,f) -> (nm,) <$> addRANFun needRANsTyCons iddefs f) (M.toList fundefs)
  new_fns <- mapM (genRelOffsetsFunNameFn needRANsTyCons ddefs) (M.elems ddefs)
  let funs' = (M.fromList funs) `M.union`
              (M.fromList $ L.map (\f -> (funName f, f)) new_fns)
  mainExp' <-
    case mainExp of
      Just (ex,ty) -> Just <$> (,ty) <$> addRANExp needRANsTyCons iddefs M.empty ex
      Nothing -> return Nothing
  let l1 = prg { ddefs = iddefs
               , fundefs = funs'
               , mainExp = mainExp'
               }
  pure l1

addRANFun :: S.Set TyCon -> DDefs Ty1 -> FunDef1 -> PassM FunDef1
addRANFun needRANsTyCons ddfs fd@FunDef{funBody} = do
  bod <- addRANExp needRANsTyCons ddfs M.empty funBody
  return $ fd{funBody = bod}

addRANExp :: S.Set TyCon -> DDefs Ty1 -> RANEnv -> Exp1 -> PassM Exp1
addRANExp needRANsTyCons ddfs ienv ex =
  case ex of
    -- Update a data constructor to produce values with random access nodes.
    -- N.B. It always uses absolute pointers for random access nodes. We
    -- may not always want this. If we know that a region is BigInf, we should
    -- use relative offsets as pointers. But that's not being done right now.
    DataConE loc dcon args ->
      case numRANsDataCon ddfs dcon of
        0 -> return ex
        n ->
          let tycon = getTyOfDataCon ddfs dcon
          -- Only add random access nodes to the data types that need it.
          in if not (tycon `S.member` needRANsTyCons)
             then return ex
             else do
          let tys = lookupDataCon ddfs dcon
              firstPacked = fromJust $ L.findIndex isPackedTy tys
              -- n elements after the first packed one require RAN's.
              needRANsExp = L.take n $ L.drop firstPacked args

          rans <- mkRANs ienv needRANsExp
          let ranArgs = L.map (\(v,_,_,_) -> VarE v) rans
          return $ mkLets rans (DataConE loc (toAbsRANDataCon dcon) (ranArgs ++ args))

    -- standard recursion here
    VarE{}    -> return ex
    LitE{}    -> return ex
    FloatE{}  -> return ex
    LitSymE{} -> return ex
    AppE f locs args -> AppE f locs <$> mapM go args
    PrimAppE f args  -> PrimAppE f <$> mapM go args
    LetE (v,loc,ty,rhs) bod -> do
      LetE <$> (v,loc,ty,) <$> go rhs <*> go bod
    IfE a b c  -> IfE <$> go a <*> go b <*> go c
    MkProdE xs -> MkProdE <$> mapM go xs
    ProjE i e  -> ProjE i <$> go e
    CaseE scrt mp -> CaseE scrt <$> concat <$> mapM docase mp
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    WithArenaE v e -> do
      e' <- go e
      return $ WithArenaE v e'
    SpawnE f locs args -> SpawnE f locs <$> mapM go args
    SyncE   -> pure SyncE
    Ext _   -> return ex
    MapE{}  -> error "addRANExp: TODO MapE"
    FoldE{} -> error "addRANExp: TODO FoldE"

  where
    go = addRANExp needRANsTyCons ddfs ienv

    changeSpawnToApp :: Exp1 -> Exp1
    changeSpawnToApp ex1 =
      case ex1 of
        VarE{}    -> ex1
        LitE{}    -> ex1
        FloatE{}  -> ex1
        LitSymE{} -> ex1
        AppE f locs args -> AppE f locs $ map changeSpawnToApp args
        PrimAppE f args  -> PrimAppE f $ map changeSpawnToApp args
        LetE (_,_,_,SyncE) bod -> changeSpawnToApp bod
        LetE (v,loc,ty,rhs) bod -> do
          LetE (v,loc,ty, changeSpawnToApp rhs) (changeSpawnToApp bod)
        IfE a b c  -> IfE (changeSpawnToApp a) (changeSpawnToApp b) (changeSpawnToApp c)
        MkProdE xs -> MkProdE $ map changeSpawnToApp xs
        ProjE i e  -> ProjE i $ changeSpawnToApp e
        DataConE loc dcon args -> DataConE loc dcon $ map changeSpawnToApp args
        CaseE scrt mp ->
          CaseE (changeSpawnToApp scrt) $ map (\(a,b,c) -> (a,b, changeSpawnToApp c)) mp
        TimeIt e ty b  -> TimeIt (changeSpawnToApp e) ty b
        WithArenaE v e -> WithArenaE v (changeSpawnToApp e)
        SpawnE f locs args -> AppE f locs $ map changeSpawnToApp args
        SyncE   -> SyncE
        Ext{}   -> ex1
        MapE{}  -> error "addRANExp: TODO MapE"
        FoldE{} -> error "addRANExp: TODO FoldE"

    docase :: (DataCon, [(Var,())], Exp1) -> PassM [(DataCon, [(Var,())], Exp1)]
    docase (dcon,vs,bod) = do
      -- Always process the body, because it might have another case expression.
      bod0 <- addRANExp needRANsTyCons ddfs ienv (changeSpawnToApp bod)
      let old_pat = (dcon,vs,bod0)
      case numRANsDataCon ddfs dcon of
        0 -> pure [old_pat]
        n -> do
          let tycon = getTyOfDataCon ddfs dcon
          -- Not all types have random access nodes.
          if not (tycon `S.member` needRANsTyCons)
          then pure [old_pat]
          else do
            absRanVars <- mapM (\_ -> gensym "absran") [1..n]
            sizeVar <- gensym "size"
            relRanVars <- mapM (\_ -> gensym "relran") [1..n]
            let relRanVars' = sizeVar : relRanVars
            let tys = lookupDataCon ddfs dcon
                -- See Note [Reusing RAN's in case expressions]
                -- We update the environment to track RAN's of the
                -- variables bound by this pattern.
                firstPacked = fromJust $ L.findIndex isPackedTy tys
                haveRANsFor = L.take n $ L.drop firstPacked $ L.map fst vs
                ienv' = M.union ienv (M.fromList $ zip haveRANsFor absRanVars)
                ienv'' = M.union ienv (M.fromList $ zip haveRANsFor relRanVars)
            bod' <- addRANExp needRANsTyCons ddfs ienv' bod
            bod'' <- addRANExp needRANsTyCons ddfs ienv'' bod
            let abs_ran_clause = (toAbsRANDataCon dcon, (L.map (,()) absRanVars) ++ vs, bod')
            let rel_ran_clause = (toRelRANDataCon dcon, (L.map (,()) relRanVars') ++ vs, bod'')
            pure [abs_ran_clause,rel_ran_clause]

-- | Update data type definitions to include random access nodes.
withRANDDefs :: Out a => S.Set TyCon -> DDefs (UrTy a) -> DDefs (UrTy a)
withRANDDefs needRANsTyCons ddfs = M.map go ddfs
  where
    -- go :: DDef a -> DDef b
    go dd@DDef{dataCons} =
      let dcons' = L.foldr (\(dcon,tys) acc ->
                              case numRANsDataCon ddfs dcon of
                                0 -> acc
                                n -> -- Not all types have random access nodes.
                                     if not (getTyOfDataCon ddfs dcon `S.member` needRANsTyCons)
                                     then acc
                                     else
                                       let tys'   = [(False,CursorTy) | _ <- [1..n]] ++ tys
                                           dcon'  = toAbsRANDataCon dcon

                                           tys''  = (False,IntTy) : [(False,IntTy) | _ <- [1..n]] ++ tys
                                           dcon'' = toRelRANDataCon dcon
                                       in [(dcon',tys'),(dcon'',tys'')] ++ acc)
                   [] dataCons
      -- Add the new constructors after all the existing constructors.
      -- The order of constructors matters when these become numeric tags after codegen.
      -- Adding new ones after all the old ones ensures that files that were
      -- serialized using a datatype before continue to work even after this datatype
      -- is updated to have random access capabilities.
      in dd {dataCons = dataCons ++ dcons'}


-- | The number of nodes needed by a 'DataCon' for full random access
-- (which is equal the number of arguments occurring after the first packed type).
--
numRANsDataCon :: Out a => DDefs (UrTy a) -> DataCon -> Int
numRANsDataCon ddfs dcon
  | isAbsRANDataCon dcon || isRelRANDataCon dcon = 0
  | otherwise =
    case L.findIndex isPackedTy tys of
      Nothing -> 0
      Just firstPacked -> (length tys) - firstPacked - 1
    where tys = lookupDataCon ddfs dcon

{-

Given a list of expressions, generate random access nodes for them.
Consider this constructor:

    (B (x : Foo) (y : Int) (z : Foo) ...)

We need two random access nodes here, for y and z. The RAN for y
is the end of x, which is a packed datatype. So we use RequestEndOf as a
placeholder here and have Cursorize replace it with the appropriate cursor.
The RAN for z is (starting address of y + 8). Or, (ran_y + 8). We use a
hacky L1 primop, AddCursorP for this purpose.

'mb_most_recent_ran' in the fold below tracks most recent random access nodes.

-}
mkRANs :: RANEnv -> [Exp1] -> PassM [(Var, [()], Ty1, Exp1)]
mkRANs ienv needRANsExp =
  snd <$> foldlM (\(mb_most_recent_ran, acc) arg -> do
          i <- gensym "ran"
          -- See Note [Reusing RAN's in case expressions]
          let rhs = case arg of
                      VarE x -> case M.lookup x ienv of
                                  Just v  -> VarE v
                                  Nothing -> PrimAppE RequestEndOf [arg]
                      -- It's safe to use 'fromJust' here b/c we would only
                      -- request a RAN for a literal iff it occurs after a
                      -- packed datatype. So there has to be random access
                      -- node that's generated before this.
                      LitE{}    -> Ext (L1.AddFixed (fromJust mb_most_recent_ran) (fromJust (sizeOfTy IntTy)))
                      FloatE{}  -> Ext (L1.AddFixed (fromJust mb_most_recent_ran) (fromJust (sizeOfTy FloatTy)))
                      LitSymE{} -> Ext (L1.AddFixed (fromJust mb_most_recent_ran) (fromJust (sizeOfTy SymTy)))
                      -- LitE{}    -> PrimAppE RequestEndOf [arg]
                      -- LitSymE{} -> PrimAppE RequestEndOf [arg]
                      oth -> error $ "addRANExp: Expected trivial expression, got: " ++ sdoc oth
          return (Just i, acc ++ [(i,[],CursorTy, rhs)]))
  (Nothing, []) needRANsExp

--------------------------------------------------------------------------------

-- See Note [When does a type needsLRAN]
-- | Collect all types that need random access nodes to be compiled.
needsRAN :: Prog2 -> S.Set TyCon
needsRAN Prog{ddefs,fundefs,mainExp} =
  let funenv = initFunEnv fundefs

      dofun FunDef{funArgs,funTy,funBody} =
        let inlocs = inLocVars funTy
            eff = arrEffs funTy
        in if S.null ((S.fromList inlocs) `S.difference` (S.map (\(Traverse v) -> v) eff)) && not (hasParallelism funTy)
             then S.empty
             else let tyenv = M.fromList $ zip funArgs (inTys funTy)
                      env2 = Env2 tyenv funenv
                      renv = M.fromList $ L.map (\lrm -> (lrmLoc lrm, regionToVar (lrmReg lrm))) (locVars funTy)
                  in needsRANExp ddefs fundefs env2 renv M.empty [] funBody

      funs = M.foldr (\f acc -> acc `S.union` dofun f) S.empty fundefs

      mn   = case mainExp of
               Nothing -> S.empty
               Just (e,_ty) -> let env2 = Env2 M.empty funenv
                               in needsRANExp ddefs fundefs env2 M.empty M.empty [] e
  in S.union funs mn

-- Maps a location to a region
type RegEnv = M.Map LocVar Var
type TyConEnv = M.Map LocVar TyCon

needsRANExp :: DDefs Ty2 -> FunDefs2 -> Env2 Ty2 -> RegEnv -> TyConEnv -> [[LocVar]] -> Exp2 -> S.Set TyCon
needsRANExp ddefs fundefs env2 renv tcenv parlocss ex =
  case ex of
    CaseE (VarE scrt) brs -> let PackedTy tycon tyloc = lookupVEnv scrt env2
                                 reg = renv # tyloc
                             in S.unions $ L.map (docase tycon reg env2 renv tcenv parlocss) brs

    CaseE scrt _ -> error $ "needsRANExp: Scrutinee is not flat " ++ sdoc scrt

    -- Standard recursion here (ASSUMPTION: everything is flat)
    VarE{}     -> S.empty
    LitE{}     -> S.empty
    FloatE{}   -> S.empty
    LitSymE{}  -> S.empty
    -- We do not process the function body here, assuming that the main analysis does it.
    AppE{}     -> S.empty
    PrimAppE{} -> S.empty

{-

If we have an expression:

    case blah of
      C x y z ->
        a = spawn (foo x)
        b = spawn (foo y)
        c = spawn (foo z)
        sync
        ...

we need to be able to access x, y and z in parallel, and thus need random access
for the type 'blah'. To spot these cases, we look at the regions in which
x, y and z live. In this case expression, they would all be in 1 single region.
So we say that if there are any region that is shared among the things in 'par',
we need random access for that type.

-}
    LetE (v,_,ty,rhs@(SpawnE{})) bod ->
      let mp   = parAppLoc env2 rhs
          locs = M.keys mp
          parlocss' = locs : parlocss
      in needsRANExp ddefs fundefs (extendVEnv v ty env2) renv (mp `M.union` tcenv) parlocss' bod

    LetE (v,_,ty,SyncE) bod ->
      let s_bod = needsRANExp ddefs fundefs (extendVEnv v ty env2) renv tcenv [] bod
          regss = map (map (renv #)) parlocss
          deleteAt idx xs = let (lft, (_:rgt)) = splitAt idx xs
                            in lft ++ rgt
          common_regs = S.unions $ map
                          (\(i,rs) -> let all_other_regs = concat (deleteAt i regss)
                                      in S.intersection (S.fromList rs) (S.fromList all_other_regs))
                          (zip [0..] regss)
      in if S.null common_regs
         then S.empty
         else let want_ran_locs = L.filter (\lc -> (renv # lc) `S.member` common_regs) (concat parlocss)
              in s_bod `S.union` (S.fromList $ map (tcenv #) want_ran_locs)

    SpawnE{} -> error "needsRANExp: Unbound SpawnE"
    SyncE    -> error "needsRANExp: Unbound SyncE"

    LetE(v,_,ty,rhs) bod -> go rhs `S.union`
                            needsRANExp ddefs fundefs (extendVEnv v ty env2) renv tcenv parlocss bod
    IfE _a b c -> go b `S.union` go c
    MkProdE{}  -> S.empty
    ProjE{}    -> S.empty
    DataConE{} -> S.empty
    TimeIt{}   -> S.empty
    WithArenaE{} -> S.empty

    Ext ext ->
      case ext of
        LetRegionE _ bod -> go bod
        LetLocE loc rhs bod  ->
            let reg = case rhs of
                        StartOfLE r  -> regionToVar r
                        InRegionLE r -> regionToVar r
                        AfterConstantLE _ lc   -> renv # lc
                        AfterVariableLE _ lc _ -> renv # lc
                        FromEndLE lc           -> renv # lc -- TODO: This needs to be fixed
                        FreeLE -> error "addRANExp: FreeLE not handled"
            in needsRANExp ddefs fundefs env2 (M.insert loc reg renv) tcenv parlocss bod
        _ -> S.empty
    MapE{}     -> S.empty
    FoldE{}    -> S.empty
  where
    go = needsRANExp ddefs fundefs env2 renv tcenv parlocss

    -- Collect all the 'Tycon's which might random access nodes
    docase tycon reg env21 renv1 tcenv1 parlocss1 br@(dcon,vlocs,bod) =
      let (vars,locs) = unzip vlocs
          renv' = L.foldr (\lc acc -> M.insert lc reg acc) renv1 locs
          env21' = extendPatternMatchEnv dcon ddefs vars locs env21
          ran_for_scrt = case (needsTraversalCase ddefs fundefs env2 br) of
                           Nothing -> S.empty
                           Just{}  -> S.singleton tycon
      in ran_for_scrt `S.union` needsRANExp ddefs fundefs env21' renv' tcenv1 parlocss1 bod

    -- Return the location and tycon of an argument to a function call.
    parAppLoc :: Env2 Ty2 -> Exp2 -> M.Map LocVar TyCon
    parAppLoc env21 (SpawnE _ _ args) =
      let fn (PackedTy dcon loc) = [(loc, dcon)]
          fn (ProdTy tys1) = L.concatMap fn tys1
          fn _ = []

          tys = map (gRecoverType ddefs env21) args
      in M.fromList (concatMap fn tys)
    parAppLoc _ oth = error $ "parAppLoc: Cannot handle "  ++ sdoc oth

--------------------------------------------------------------------------------

{-| Given a datatype, generate a copy-like function. But instead of just copying
the input value, it udpates constructors to have size information, and also
relative offsets. Assumes that this function will always be called on a value
written to a contiguous region. Chunked regions are not supported.

For example, for the Tree datatype it'll generate a function like this:

data Tree = Leaf Int | Node Tree Tree | Node* Int Int Tree Tree

_add_size_and_rel_offsets_Tree :: Tree -> Tree
_add_size_and_rel_offsets_Tree tr =
  case tr of
    Leaf i          -> Leaf i
    Node left right ->
      let left'  = _add_size_and_rel_offsets_Tree left
          right' = _add_size_and_rel_offsets_Tree right
          size   = sizeof(left') + sizeof(right') + 1 + 8 + 8
          offset_right = sizeof(left')
      in Node* size offset_right left' right'

For a different datatype;

data Foo = K1 | K2 Foo Foo Foo | K2* Int Int Int Tree Tree Tree

_add_size_and_rel_offsets_Foo :: Foo -> Foo
_add_size_and_rel_offsets_Foo foo =
  case foo of
    K1 -> K1
    K2 a b c ->
      let a' = _add_size_and_rel_offsets_Foo a
          b' = _add_size_and_rel_offsets_Foo b
          c' = _add_size_and_rel_offsets_Foo c
          size = 1 + 8 + 8 + 8 + sizeof(a') + sizeof(b') + sizeof(c')
          offset_b = 8 + sizeof(a')
          offset_c = sizeof(a') + sizeof(b')
      in K2* size offset_b offset_c a' b' c'

-}
genRelOffsetsFunNameFn :: S.Set TyCon -> DDefs Ty1 -> DDef Ty1 -> PassM FunDef1
genRelOffsetsFunNameFn needRANsTyCons ddfs DDef{tyName, dataCons} = do
  arg <- gensym $ "arg"
  casebod <- forM dataCons $ \(dcon, dtys) ->
             do let tys = L.map snd dtys
                xs <- mapM (\_ -> gensym "x") tys
                ys <- mapM (\_ -> gensym "y") tys
                let num_offsets = numRANsDataCon ddfs dcon
                bod <- do
                       let bod0 acc = foldr (\(ty,x,y) acc ->
                                               if isPackedTy ty
                                               then LetE (y, [], ty, AppE (mkRelOffsetsFunName (tyToDataCon ty)) [] [VarE x]) acc
                                               else LetE (y, [], ty, VarE x) acc)
                                            acc
                                            (L.zip3 tys xs ys)
                       if not (S.member (fromVar tyName) needRANsTyCons) then return $ bod0 (DataConE () dcon (map VarE ys))
                       else if num_offsets == 0
                       -- Nothing much to do. Just recursively process all the packed arguments.
                       then return $ bod0 (DataConE () dcon (map VarE ys))
                       -- We have to add a size field, and offsets in addition to recursively processing
                       -- the packed arguments.
                       else do
                         size_vars <- mapM (\y -> gensym $ toVar $ "sizeof_" ++ fromVar y ++ "_") ys
                         let size_binds acc = foldr
                                                (\(sz,y,ty) acc ->
                                                     if isPackedTy ty
                                                     then LetE (sz,[],IntTy,PrimAppE RequestSizeOf [VarE y]) acc
                                                     else LetE (sz,[],IntTy,LitE (fromJust $ sizeOfTy ty)) acc)
                                                acc (L.zip3 size_vars ys tys)
                         offset_vars <- mapM (\_ -> gensym "offset_") [0..(num_offsets-1)]
                         let need_offsets = reverse $ L.take num_offsets (reverse xs)
                         let addp ls = case ls of
                                         []       -> LitE 0
                                         (x:y:[]) -> PrimAppE AddP [VarE x, VarE y]
                                         (x:rst)  -> PrimAppE AddP [VarE x, addp rst]
                         let offset_binds acc = foldr
                                                  (\(ov, x) acc ->
                                                     let idx_of_x    = fromJust $ L.elemIndex x xs
                                                         idx_of_ov   = fromJust $ L.elemIndex ov offset_vars
                                                         offsets_infront = length (L.drop idx_of_ov offset_vars) - 1
                                                         have_to_add = L.take idx_of_x size_vars
                                                         rhs = PrimAppE AddP [LitE $ (fromJust (sizeOfTy IntTy)) * offsets_infront,
                                                                              addp have_to_add]
                                                     in LetE (ov,[],IntTy,rhs) acc)
                                                  acc (zip offset_vars need_offsets)
                         dcon_size <- gensym "size_dcon"
                         let size_offsets = LitE $ 1 + (fromJust (sizeOfTy IntTy)) * length offset_vars
                             dcon_size_bind acc = LetE (dcon_size,[],IntTy, PrimAppE AddP [size_offsets, addp size_vars] ) acc
                             dcon_args = [dcon_size] ++ offset_vars ++  ys
                             dcon' = toRelRANDataCon dcon
                         pure $ bod0 $ size_binds $ offset_binds $ dcon_size_bind $ DataConE () dcon' (map VarE dcon_args)
                return (dcon, L.map (\x -> (x,())) xs, bod)

  return $ FunDef { funName = mkRelOffsetsFunName (fromVar tyName)
                  , funArgs = [arg]
                  , funTy   = ( [PackedTy (fromVar tyName) ()], PackedTy (fromVar tyName) () )
                  , funBody = CaseE (VarE arg) casebod
                  , funRec = Rec
                  , funInline = NoInline
                  }
