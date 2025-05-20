{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE CPP              #-}
{-# LANGUAGE RecordWildCards  #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- | Insert end witnesses in an L2 program by changing function types,
-- and updating expressions to pass (second-class) end locations around
-- via RetE in tail position and an extended binding form in LetE.
-- Assumes that expressions are flattened and in ANF, and that location
-- symbols are all unique! Failure to meet these assumptions will cause
-- this pass to fail or possibly produce wrong output.
--
--- Steps:
---
--- 1. For each function type, inspect its input parameter type and traversal
---    effect to determine which packed arguments are completely traversed,
---    and update the type to indicate that the EndOf witness for each
---    of these traversed arguments is returned.
---
--- 2. For each function body, walk through the let spine, updating bindings
---    to include locations returned as end witnesses, and add coersions from
---    EndOf witnesses to expected locations. Upon reaching tail position,
---    emit a RetE form and compute what the proper EndOf locations are.
---
--- 3. For the main body, do the same thing minus inserting the RetE in tail
---    position.

module Gibbon.Passes.RouteEnds
    ( routeEnds ) where

import qualified Data.List as L
import qualified Safe as Sf
import Data.Maybe ( fromJust )
import Data.Map as M
import Data.Set as S
import Control.Monad

import Data.Foldable ( foldrM, foldlM )

import Gibbon.Common
import Gibbon.L2.Syntax as L2
import Gibbon.L1.Syntax as L1
import Control.Arrow (Arrow(first))
import Gibbon.L0.Typecheck (instDataConTy)
import GHC.Generics
import Text.PrettyPrint.GenericPretty


-- | Data structure that accumulates what we know about the relationship
-- between locations and EndOf witnesses.
--
-- Performing a lookup (to find the end of a given location) will first check
-- if there exists a mapping in the endOf map for that location, then will check
-- if there exists a mapping in the equivTo map, and if so will recur to find
-- the end of that location.
--
-- This is used for when we perform pattern matching. The end of some binary tree
-- (for example) is the same as the end of its second node, so we want to record
-- that knowledge as we traverse the AST.
data EndOfRel = EndOfRel
    {
      endOf :: M.Map LocVar LocVar -- ^ Map a location to it's EndOf witness
    , equivTo :: M.Map LocVar LocVar -- ^ Map of a location to a known equivalent location
    }
  deriving (Eq, Ord, Read, Show)

data DelayedExpr = LetExpr (Var, [LocVar], Ty2, Exp2)
                 | LetLocExpr LocVar LocExp 
                    deriving (Eq, Ord, Show, Generic)

instance Out DelayedExpr

-- | Create an empty EndOfRel
emptyRel :: EndOfRel
emptyRel = EndOfRel M.empty M.empty

-- | Assert that one location's end is equivalent to another's end.
-- Order is important here: we expect to look up the end of the first
-- location argument, not the second.
mkEqual :: LocVar -> LocVar -> EndOfRel -> EndOfRel
mkEqual l1 l2 EndOfRel{endOf,equivTo} =
    EndOfRel{endOf=endOf,equivTo=M.insert l1 l2 equivTo}

-- | Assert that we have found an EndOf relation between two locations.
mkEnd :: LocVar -> LocVar -> EndOfRel -> EndOfRel
mkEnd l1 l2 EndOfRel{endOf,equivTo} =
    EndOfRel{endOf=M.insert l1 l2 endOf,equivTo=equivTo}

-- | Look up the end of a location.
findEnd :: LocVar -> EndOfRel -> LocVar
findEnd l EndOfRel{endOf,equivTo} =
    case M.lookup l endOf of -- Can we immediately look up the end of l?
      Nothing -> case M.lookup l equivTo of -- Is there an equivalent location to use?
                   Nothing -> error $ "Failed finding the end of " ++ (show l)
                   Just leq -> findEnd leq EndOfRel{endOf,equivTo}
      Just lend -> lend

eorAppend :: EndOfRel -> EndOfRel -> EndOfRel
eorAppend eor1 eor2 =
    EndOfRel { endOf   = (endOf eor1) `M.union` (endOf eor2)
             , equivTo = (equivTo eor1) `M.union` (equivTo eor2) }

instance Monoid EndOfRel where
  mempty  = emptyRel

#if !(MIN_VERSION_base(4,11,0))
  mappend = eorAppend
#endif

instance Semigroup EndOfRel where
  (<>) = eorAppend

bindReturns :: Exp2 -> PassM Exp2
bindReturns ex =
  case ex of
    VarE v -> pure (VarE v)
    LitE{} -> handleScalarRet ex id
    CharE{} -> handleScalarRet ex id
    FloatE{} -> handleScalarRet ex id
    LitSymE{} -> handleScalarRet ex id
    AppE{} -> pure ex
    PrimAppE p _ ->
      case p of
        MkTrue -> handleScalarRet ex id
        MkFalse -> handleScalarRet ex id
        _ -> pure ex
    LetE (v,locs,ty,rhs) bod | isScalar bod -> do
      handleScalarRet bod (\bod' -> LetE (v,locs,ty,rhs) bod')

    LetE (v,locs,ty,rhs) bod -> do
      -- rhs' <- bindReturns rhs
      bod' <- bindReturns bod
      pure $ LetE (v,locs,ty,rhs) bod'

    IfE a b c  -> do
      a' <- bindReturns a
      b' <- bindReturns b
      c' <- bindReturns c
      pure $ IfE a' b' c'
    MkProdE{} -> pure ex
    ProjE{} -> pure ex
    CaseE scrt brs -> do
      scrt' <- bindReturns scrt
      CaseE scrt' <$> (mapM (\(a,b,c) -> (a,b,) <$> bindReturns c) brs)
    DataConE{} -> pure ex
    TimeIt{} -> pure ex
    SpawnE{} -> pure ex
    SyncE -> pure ex
    WithArenaE v e -> do
      e' <- bindReturns e
      pure $ WithArenaE v e'
    Ext ext ->
      case ext of
        LetRegionE r sz ty bod -> do
          bod' <- bindReturns bod
          pure $ Ext $ LetRegionE r sz ty bod'
        LetParRegionE r sz ty bod -> do
          bod' <- bindReturns bod
          pure $ Ext $ LetParRegionE r sz ty bod'
        LetLocE loc locexp bod -> do
          bod' <- bindReturns bod
          pure $ Ext $ LetLocE loc locexp bod'
        L2.StartOfPkdCursor{}-> pure ex
        L2.TagCursor{}-> pure ex
        RetE{} -> pure ex
        L2.AddFixed{} -> pure ex
        FromEndE{} -> pure ex
        BoundsCheck{}  -> pure ex
        IndirectionE{} -> pure ex
        GetCilkWorkerNum-> pure ex
        LetAvail a bod  -> do
          bod' <- bindReturns bod
          pure $ Ext $ LetAvail a bod'
        AllocateTagHere{} -> pure ex
        AllocateScalarsHere{} -> pure ex
        SSPush{} -> pure ex
        SSPop{} -> pure ex
    MapE{}  -> error $ "bindReturns: TODO MapE"
    FoldE{} -> error $ "bindReturns: TODO FoldE"

handleScalarRet :: Exp2 -> (Exp2 -> Exp2) -> PassM Exp2
handleScalarRet bod fn = do
  let bind_and_recur bind_e bind_ty = do
        tmp <- gensym "fltScalar"
        let e1 = (LetE (tmp,[],bind_ty,bind_e) (VarE tmp))
        pure $ fn e1
  case bod of
    LitE n -> bind_and_recur (LitE n) IntTy
    CharE n -> bind_and_recur (CharE n) CharTy
    FloatE n -> bind_and_recur (FloatE n) FloatTy
    LitSymE n -> bind_and_recur (LitSymE n) SymTy
    PrimAppE MkTrue [] -> bind_and_recur (PrimAppE MkTrue []) BoolTy
    PrimAppE MkFalse [] -> bind_and_recur (PrimAppE MkFalse []) BoolTy
    _ -> pure $ fn bod
    -- _ -> error $ "RouteEnds: Not scalar " ++ sdoc bod

isScalar :: Exp2 -> Bool
isScalar e1 =
  case e1 of
    LitE{} -> True
    CharE{} -> True
    FloatE{} -> True
    LitSymE{} -> True
    PrimAppE MkTrue [] -> True
    PrimAppE MkFalse [] -> True
    _ -> False

-- | Process an L2 Prog and thread through explicit end-witnesses.
-- Requires Gensym and runs in PassM. Assumes the Prog has been flattened.
routeEnds :: Prog2 -> PassM Prog2
routeEnds prg@Prog{ddefs,fundefs,mainExp} = do

  -- Handle functions in two steps (to account for mutual recursion):
  --
  -- First, compute the new types, and build a new fundefs structure:
  fds' <- mapM fdty $ M.elems fundefs
  let fundefs' = M.fromList $ L.map (\f -> (funName f,f)) fds'
  -- Then process the actual function bodies using the new fundefs structure:
  fds'' <- mapM (fd fundefs') fds'
  let fundefs'' = M.fromList $ L.map (\f -> (funName f,f)) fds''
      env2 = progToEnv' prg
  -- Handle the main expression (if it exists):
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (e,t) -> do e' <- bindReturns e
                                 e'' <- exp M.empty fundefs'' [] emptyRel M.empty M.empty env2 e'
                                 return $ Just (e'',t)

  -- Return the updated Prog
  return $ Prog ddefs fundefs'' mainExp'


  where
    -- Helper functions:

    -- | Process function types (but don't handle bodies)
    fdty :: L2.FunDef2 -> PassM L2.FunDef2
    fdty FunDef{funName,funTy,funArgs,funBody,funMeta} =
        do let (ArrowTy2 locin tyin eff tyout _locout isPar) = funTy
               handleLoc (LRM l r m) ls = if S.member (Traverse l) eff then (LRM l r m):ls else ls
               locout' = L.map EndOf $ L.foldr handleLoc [] locin
           return FunDef{funName,funTy=(ArrowTy2 locin tyin eff tyout locout' isPar),funArgs,funBody,funMeta}


    -- | Process function bodies
    fd :: FunDefs2 -> L2.FunDef2 -> PassM L2.FunDef2
    fd fns FunDef{funName,funTy,funArgs,funBody,funMeta} =
        do let (ArrowTy2 locin tyins eff _tyout _locout _isPar) = funTy
               handleLoc (LRM l _r _m) ls = if S.member (Traverse l) eff then l:ls else ls
               retlocs = L.foldr handleLoc [] locin
               funArgs' = L.map fromVarToFreeVarsTy funArgs
               lenv = L.foldr
                        (\(a,t) acc -> case t of
                                         PackedTy _ loc -> M.insert a loc acc
                                         _ -> acc)
                        M.empty (zip funArgs' tyins)
               pakdLocs = concatMap
                            (\t -> case t of
                                     PackedTy _ loc -> [((fromLocVarToFreeVarsTy loc), t)]
                                     ProdTy ys -> pakdLocs ys
                                     _ -> [])
               initVEnv = M.fromList $ pakdLocs tyins ++ zip funArgs' tyins
               env2 = Env2 initVEnv (initFunEnv' fundefs)
           funBody' <- bindReturns funBody
           funBody'' <- exp M.empty fns retlocs emptyRel lenv M.empty env2 funBody'
           return FunDef{funName,funTy,funArgs,funBody=funBody'',funMeta}


    -- | Process expressions.
    -- Takes the following arguments:
    -- 1. A function definition map
    -- 2. a list of locations we need to return the ends of
    -- 3. an end-of relation
    -- 4. a map of var to location
    -- 5. a map from location to location after it
    -- 6. the expression to process
    
    exp :: M.Map LocVar [DelayedExpr] -> FunDefs2 -> [LocVar] -> EndOfRel -> M.Map FreeVarsTy LocVar ->
           M.Map FreeVarsTy LocVar -> Env2 FreeVarsTy Ty2 -> Exp2 -> PassM Exp2
    exp inst_waiting_on_loc fns retlocs eor lenv afterenv env2 e =
        case e of

          -- Variable case, *should* be the base case assuming our expression was
          -- properly put in ANF.
          -- We generate our RetE form here. By this point we should know the ends
          -- of each of the locactions in relocs.

          -- we fmap location at the top-level case expression
          VarE v -> mkRet retlocs $ VarE v

          -- -- If a function has a literal as it's tail, it cannot return any
          -- -- end witnesses (since only VarE forms are converted to RetE's).
          -- -- We therefore bind that literal to a variable, and recur. We need
          -- -- to handle LetRegionE and LetLocE similarly.
          -- LetE (v,ls,ty,rhs) bod | isScalar bod -> do
          --   handleScalarRet bod (\bod' -> LetE (v,ls,ty,rhs) bod')

          -- Ext (LetRegionE r bod) | isScalar bod -> do
          --   handleScalarRet bod (\bod' -> Ext (LetRegionE r bod'))

          -- Ext (LetLocE v locexp bod) | isScalar bod -> do
          --   handleScalarRet bod (\bod' -> Ext (LetLocE v locexp bod'))

          -- This is the most interesting case: a let bound function application.
          -- We need to update the let binding's extra location binding list with
          -- the end witnesses returned from the function.
          LetE (v,_ls,ty,(AppE f lsin e1)) e2 -> do
                 let lenv' = case ty of
                               PackedTy _n l -> M.insert (fromVarToFreeVarsTy v) l lenv
                               _ -> lenv

                 (outlocs,newls,eor') <- doBoundApp f lsin
                 let (e2', inst_waiting_on_loc', rel) = wrapBody f e2 newls inst_waiting_on_loc 

                 e2'' <- exp inst_waiting_on_loc' fns retlocs eor' lenv' afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) e2'
                 let expr = dbgTrace (minChatLvl) "Print insts_waiting_on_loc: " dbgTrace (minChatLvl) (sdoc (newls, (v,_ls,ty,(AppE f lsin e1)), inst_waiting_on_loc', rel)) dbgTrace (minChatLvl) "End print insts waiting on loc.\n"  LetE (v,outlocs,ty, AppE f lsin e1) e2''
                 return $ L.foldr (\lete acc -> case lete of 
                                                  LetExpr (v,ls,ty,rhs) -> LetE (v,ls,ty,rhs) acc
                                                  LetLocExpr loc locexp -> Ext $ LetLocE loc locexp acc
                                  ) expr (L.nub rel)              

          -- Exactly like AppE.
          LetE (v,_ls,ty,(SpawnE f lsin e1)) e2 -> do
                 let lenv' = case ty of
                               PackedTy _n l -> M.insert (fromVarToFreeVarsTy v) l lenv
                               _ -> lenv
                 (outlocs,newls,eor') <- doBoundApp f lsin
                 let (e2', inst_waiting_on_loc', rel) = wrapBody f e2 newls inst_waiting_on_loc
                 e2'' <- exp inst_waiting_on_loc' fns retlocs eor' lenv' afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) e2'
                 return $ LetE (v,outlocs,ty, SpawnE f lsin e1) e2''
                               

          SpawnE{} -> error "routeEnds: Unbound SpawnE"
          SyncE    -> pure e

          CaseE (VarE x) brs -> do
                 -- We will need to gensym while processing the case clauses, so
                 -- it has to be in the PassM monad
                 brs' <-
                     forM brs $ \(dc, vls, e) ->
                       case vls of
                         [] ->
                           case (M.lookup (fromVarToFreeVarsTy x) lenv) of
                             Just l1 -> do
                               l2 <- freshCommonLoc "jump" l1
                               let l2loc = l2
                                   eor' = mkEnd l1 l2loc eor
                                   e' = case l1 of 
                                            Single _ -> Ext $ LetLocE l2loc (AfterConstantLE 1 l1) e
                                            SoA in_dbuf_loc in_flocs -> let in_dcon_lete = LetLocE (getDconLoc l1) (GetDataConLocSoA l1)
                                                                            end_con_lete = LetLocE (getDconLoc l2loc) (AfterConstantLE 1 ((getDconLoc l1)))
                                                                            -- generate all alias to field constraints 
                                                                            field_letes = L.concatMap (\(key, lv) -> case L.lookup key (getAllFieldLocsSoA l2loc) of 
                                                                                                                            Nothing -> error "routeEnds: expected location for field."
                                                                                                                            Just ofl -> case ofl of 
                                                                                                                                            Single _ ->  [LetLocE lv (GetFieldLocSoA key l1)]  ++ [LetLocE ofl (AfterConstantLE 0 lv)]
                                                                                                                                            SoA _ _ -> [LetLocE lv (GetFieldLocSoA key l1)]  -- ++ [LetLocE ofl (AfterConstantLE 0 lv)]
                                                                                 ) in_flocs
                                                                            field_variables_jump_loc = L.map (\((kdc, kidx), l) -> 
                                                                                                      let tyOfCon = lookupDataCon ddefs kdc
                                                                                                          in case tyOfCon !! kidx of 
                                                                                                                PackedTy _ _ -> 
                                                                                                                  let l' = case L.lookup (kdc, kidx) in_flocs of 
                                                                                                                          Nothing -> error "routeEnds: expected location for field."
                                                                                                                          Just ofl -> ofl
                                                                                                                   in ((kdc, kidx), l')  
                                                                                                                _ -> ((kdc, kidx), l)
  
                                              
                                                                               ) (getAllFieldLocsSoA l2loc)     
                                                                            new_soa_loc  = LetLocE l2loc (GenSoALoc (getDconLoc l2loc) field_variables_jump_loc )
                                                                            all_letes = [in_dcon_lete, end_con_lete] ++ field_letes ++ [new_soa_loc]  
                                                                            new_exp = L.foldr (\lete acc -> Ext $ lete acc) e all_letes
                                                                          in new_exp
                               e'' <- exp inst_waiting_on_loc fns retlocs eor' lenv (M.insert (fromLocVarToFreeVarsTy l1) l2loc lenv) env2 e'
                               return (dc, vls, e'')
                             Nothing -> error $ "Failed to find " ++ sdoc x ++ " in " ++ sdoc lenv
                         _ -> do
                          case (M.lookup (fromVarToFreeVarsTy x) lenv) of
                            Just scrutloc -> do
                              let need = snd $ last vls
                                  tyconOfDataCon = getTyOfDataCon ddefs dc
                                  argtys = lookupDataCon ddefs dc
                                  env2' = extendsVEnvLocVar (M.fromList (zip (L.map fromLocVarToFreeVarsTy locs) argtys ++ zip varsToFreeVarsTy argtys)) env2
                                  lx = case M.lookup (fromVarToFreeVarsTy x) lenv of
                                          Nothing -> error $ "Failed to find " ++ (show x)
                                          Just l -> l
                                  -- we know lx and need have the same end, since
                                  -- lx is the whole packed thing and need is its
                                  -- last field, so when we look up the end of lx
                                  -- what we really want is the end of need.
                                  eor' = mkEqual lx need eor
                                  f (l1,l2) env = M.insert l1 l2 env
                                  afterenv' = case scrutloc of
                                                Single _ -> L.foldr f afterenv $ zip (L.map (fromLocVarToFreeVarsTy . snd) vls) (Sf.tailErr $ L.map snd vls) 
                                                SoA dcloc flocs -> let 
                                                                    locations = L.map snd vls  
                                                                    self_recursive_locs_in_order = concatMap (\(v, l) -> case (lookupVEnvLocVar (V v) env2') of
                                                                                                                               PackedTy tycon _ -> if tycon == tyconOfDataCon
                                                                                                                                                then [l]
                                                                                                                                                else []          
                                                                                                                               _ -> []
                                                                                      

                                                                                                         ) vls
                                                                    afterenv_self_rec = L.foldr f afterenv $ zip (L.map FL self_recursive_locs_in_order) (Sf.tailErr self_recursive_locs_in_order) 
                                                                    -- VS: TODO what about other fields that are not self recursive and other scalar fields ? 
                                                                    -- assumption that all scalar and related packed fields are before the first self recursive fields. 
                                                                    -- TODO: this may need to change in the future.
                                                                    --let idx = L.elemIndex tup vls
                                                                    --    in case idx of 
                                                                    --    Nothing -> error ""
                                                                    --    Just idx' ->
                                                                     in case self_recursive_locs_in_order of 
                                                                                  [] -> L.foldr f afterenv $ zip (L.map (fromLocVarToFreeVarsTy . snd) vls) (Sf.tailErr $ L.map snd vls)
                                                                                  _ -> let 
                                                                                         first_self_rec = L.head self_recursive_locs_in_order  
                                                                                         (afterenv_self_rec', _) = L.foldl (\(acc, seen) tup@(v, l) -> if (l /= first_self_rec)
                                                                                                                                                       then
                                                                                                                                                         if seen == True
                                                                                                                                                         then 
                                                                                                                                                            (acc, seen)
                                                                                                                                                         else
                                                                                                                                                            case (lookupVEnvLocVar (V v) env2') of
                                                                                                                                                                PackedTy tycon _ -> (M.insert (FL l) first_self_rec acc, seen)
                                                                                                                                                                _ -> 
                                                                                                                                                                      let elem_idx = L.elemIndex tup vls
                                                                                                                                                                        in case elem_idx of 
                                                                                                                                                                              Nothing -> error ""
                                                                                                                                                                              Just idx' -> let idx'' = idx' + 1 
                                                                                                                                                                                               (_, l') = vls !! idx''
                                                                                                                                                                                            in (M.insert (FL l) l' acc, seen)
                                                                                                                                                       else (acc, True)
                                                                                                                           ) (afterenv_self_rec, False) vls
                                                                                             in afterenv_self_rec'

                                  -- afterenv' = L.foldr f afterenv $ zip (L.map (fromLocVarToFreeVarsTy . snd) vls) (Sf.tailErr $ L.map snd vls)
                                  -- two cases here for handing bound parameters:
                                  -- we have a packed type:
                                  handleLoc (eor,e) (_,(PackedTy _ _), _) = return (eor,e)
                                  -- or we have a non-packed type, and we need to "jump" over it and
                                  -- bind a location to after it
                                  handleLoc (eor,e) (l1,ty, idx) = do
                                        case scrutloc of 
                                          Single _ -> do 
                                            l2 <- gensym "jump"
                                            let l2loc = singleLocVar l2
                                            let eor' = mkEnd l1 l2loc eor
                                            let (Just jump) = L1.sizeOfTy ty
                                            let e' = Ext $ LetLocE l2loc (AfterConstantLE jump l1) e
                                            return (eor', e')
                                          _ -> error "handleLoc: did not expect an SoA location!!"
                                  
                                  {-VS: TODO: We need to see if this logic will work for scalars after packed fields.-}
                                  handleLocSoA :: (EndOfRel, Exp2) -> [(LocVar, Ty2, Int)] -> PassM (EndOfRel, Exp2)
                                  handleLocSoA (eor, e) [] = return (eor, e)
                                  handleLocSoA (eor, e) cases = do
                                    case scrutloc of
                                          -- We need to return endof locations for each non packed field
                                          -- Hence, in an SoA case, the data con location stays the same
                                          -- We just need to produce new locations for each field. 
                                          SoA in_dbuf_loc in_flocs -> do 
                                            --let jump_dloc = dloc 
                                            l2 <- freshCommonLoc "jumpf" scrutloc
                                            let final_soa_loc = l2
                                            let seenSamePackedTy = False
                                            (eor', exprs, _, bnds') <- foldlM (\(eorr, ee, seen, bnds) (l1, ty, idx)  -> do
                                                                                                 case ty of
                                                                                                    PackedTy tycon _ -> if tycon == tyconOfDataCon
                                                                                                                        then do
                                                                                                                          if seen == False
                                                                                                                          -- First time we see the same packed type.
                                                                                                                          -- Make additional lets to be safe
                                                                                                                          -- This needs more fixing 
                                                                                                                          -- for instance if you have multiple packed types that are different 
                                                                                                                          -- before.    
                                                                                                                          then do
                                                                                                                            let jump_d_loc_p = getDconLoc l1
                                                                                                                            let jump_d_final = getDconLoc final_soa_loc
                                                                                                                            let aliasLet = LetLocE jump_d_loc_p (AfterConstantLE 0 jump_d_final)
                                                                                                                            -- VS [05.11.2025]
                                                                                                                            -- It is fine to remove all locs that are scalars. 
                                                                                                                            -- In the case of an SoA transformation, all single field locs are scalars 
                                                                                                                            -- As long as we don't have a type level annotation this is fine. 
                                                                                                                            -- Later on this needs to be updated. 
                                                                                                                            -- Make lets for all the other scalar field locs
                                                                                                                            let alias_flets = L.foldr (\(k, l) acc -> case l of 
                                                                                                                                                                          Single _ -> acc ++ [LetLocE l (AfterConstantLE 0 (getFieldLoc k final_soa_loc))]
                                                                                                                                                                          SoA _ _ -> acc
                                                                                                                                                      ) [aliasLet] (getAllFieldLocsSoA l1)
                                                                                                                            return (eorr,  ee, True, bnds ++ alias_flets)
                                                                                                                          else do 
                                                                                                                            return (eorr, ee, seen, bnds)
                                                                                                                        else do
                                                                                                                          return (eorr, ee, seen, bnds)
                                                                                                    -- PackedTy tycon _ -> return (eorr, ee, seen)
                                                                                                    _ -> do
                                                                                                        let jump_loc = getFieldLoc (dc, idx) final_soa_loc
                                                                                                        -- let l2loc = l2
                                                                                                        let eorr' = mkEnd l1 jump_loc eorr
                                                                                                        let (Just jump) = L1.sizeOfTy ty
                                                                                                        let fieldCon = LetLocE (jump_loc) (AfterConstantLE jump l1)
                                                                                                        return (eorr', [fieldCon] ++ ee, seen, bnds)                                            
                                                                  ) (eor, [], seenSamePackedTy, []) cases
                                            let in_dcon_lete = LetLocE (singleLocVar in_dbuf_loc) (GetDataConLocSoA scrutloc)
                                            let end_con_lete = LetLocE (getDconLoc final_soa_loc) (AfterConstantLE 1 (singleLocVar in_dbuf_loc))
                                            --let (Just jump) = L1.sizeOfTy ty
                                            --let let_field_after = LetLocE (getFieldLoc (dc, idx) l2loc) (AfterConstantLE jump l1)
                                            --let new_field_locs = L.map (\(k, l) -> if k == (dc, idx)
                                            --                                       then (k, (getFieldLoc k l2loc))
                                            --                                       else (k, l)
                                            --                           ) $  getAllFieldLocsSoA l2loc
                                            
                                            
                                                -- generate all alias to field constraints 
                                            let (all_field_gets, unsed_assign) = L.foldr (\(key@(dc', _), lv) (lst1, lst2) -> case L.lookup key (getAllFieldLocsSoA final_soa_loc) of 
                                                                                                                      Nothing -> error "routeEnds: expected location for field."
                                                                                                                      Just ofl -> if dc' == dc
                                                                                                                                  then ([LetLocE lv (GetFieldLocSoA key scrutloc)] ++ lst1, lst2)  --[LetLocE (singleLocVar lv) (GetFieldLocSoA key scrutloc)] ++ [LetLocE (l1) (AfterConstantLE 0 (getFieldLoc (dc, idx) scrutloc))] ++ 
                                                                                                                                  else ([LetLocE lv (GetFieldLocSoA key scrutloc)] ++ lst1, [LetLocE ofl (AfterConstantLE 0 lv)] ++ lst2)
                                                   ) ([], []) in_flocs
                                            let argtys' = concatMap (\argty -> case argty of 
                                                                        PackedTy tcc _ -> if tcc /= tyconOfDataCon
                                                                                          then [argty]
                                                                                          else []
                                                                        _ -> [argty]
                                                              ) argtys
                                            -- let field_variables_jump_loc = (L.map (\((key, lv), ty) -> case ty of 
                                            --                                                                 PackedTy tyconp _  -> if tyconp /= tyconOfDataCon
                                            --                                                                                       then  
                                            --                                                                                         let lv' = L.lookup key in_flocs
                                            --                                                                                           in case lv' of
                                            --                                                                                               Nothing -> error "routeEnds: expected location for field."
                                            --                                                                                               Just ofl -> (key, ofl)
                                            --                                                                                       else (key, lv)
                                            --                                                                 _ -> (key, lv)
                                            --                                       ) $ zip (getAllFieldLocsSoA final_soa_loc) (argtys'))

                                            let field_variables_jump_loc = L.map (\((kdc, kidx), l) -> if kdc == dc
                                                                                                     then 
                                                                                                      let tyOfCon = lookupDataCon ddefs kdc
                                                                                                          in case tyOfCon !! kidx of 
                                                                                                                PackedTy _ _ -> 
                                                                                                                  let l' = case L.lookup (kdc, kidx) in_flocs of 
                                                                                                                          Nothing -> error "routeEnds: expected location for field."
                                                                                                                          Just ofl -> ofl
                                                                                                                   in ((kdc, kidx), l')  
                                                                                                                _ -> ((kdc, kidx), l)
                                                                                                     else ((kdc, kidx), l)  
                                              
                                                                               ) (getAllFieldLocsSoA final_soa_loc)
                                            let new_soa_loc  = LetLocE final_soa_loc (GenSoALoc (getDconLoc final_soa_loc) field_variables_jump_loc)
                                            let all_letes = [in_dcon_lete, end_con_lete] ++ all_field_gets ++ exprs ++ unsed_assign  ++ bnds' ++ [new_soa_loc]  
                                            let e' = L.foldr (\lete acc -> Ext $ lete acc) e all_letes
                                            --let (Just jump) = L1.sizeOfTy ty
                                            --let get_dcon_let = LetLocE (singleLocVar jump_dloc) (GetDataConLocSoA scrutloc)
                                            --let after_let = LetLocE l2loc (AfterConstantLE jump l1)
                                            --let new_field_locs = L.map (\(k, l) -> if k == (dc, idx)
                                            --                                     then (k, l2)
                                            --                                     else (k, l)
                                            --                         ) flocs 
                                            --let new_field_locs' = L.map (\(k, l) -> (k, singleLocVar l)) new_field_locs
                                            --let new_soa_loc = LetLocE (SoA jump_dloc new_field_locs) (GenSoALoc (singleLocVar jump_dloc) new_field_locs')
                                            --let e' = Ext $ get_dcon_let $ Ext $ after_let $ Ext $ new_soa_loc e
                                            -- let eor'' = mkEnd scrutloc final_soa_loc eor'
                                            -- VS: Restricts moving scalars fields at the end
                                            let eor'' = case (L.last cases) of
                                                                (l1, ty, idx) -> case ty of 
                                                                                      PackedTy{} -> eor'
                                                                                      _  -> mkEnd scrutloc final_soa_loc eor'

                                            return (eor'', e')
                                          _ -> error "handleLoc: did not expect an AoS location!!"  
                                  vars = L.map fst vls
                                  varsToFreeVarsTy = L.map fromVarToFreeVarsTy vars 
                                  locs = L.map snd vls
                                  vls' = L.map (\(v, l) -> (fromVarToFreeVarsTy v, l)) vls
                                  lenv' = M.union lenv $ M.fromList vls'
                              (eor'',e') <- case scrutloc of 
                                                  Single _ -> foldM handleLoc (eor',e) $ zip3 (L.map snd vls) argtys [0..((length vls) - 1)]
                                                  _ -> handleLocSoA (eor',e) $ zip3 (L.map snd vls) argtys [0..((length vls) - 1)]
                              e'' <- exp inst_waiting_on_loc fns retlocs eor'' lenv' afterenv' env2' e'
                              return (dc, vls, e'')
                            Nothing -> error $ "Failed to find " ++ (show x)
                 return $ CaseE (VarE x) brs'



          CaseE complex brs -> do
            let ty = gRecoverTypeLoc ddefs env2 complex
            v <- gensym "flt_RE"
            let ex = L1.mkLets [(v,[],ty,complex)] (CaseE (VarE v) brs)
            exp inst_waiting_on_loc fns retlocs eor lenv afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) ex


          -- This shouldn't happen, but as a convenience we can ANF-ify this AppE
          -- by gensyming a new variable, sticking the AppE in a LetE, and recuring.
          -- Question: should this fail instead? I'm not sure.
          AppE v args arg -> do
                 v' <- gensym "tailapp"
                 let ty = gRecoverTypeLoc ddefs env2 e
                     e' = LetE (v',[], ty, AppE v args arg) (VarE v')
                 go (e')

          PrimAppE (DictInsertP dty) [(VarE a),d,k,v] -> do
                 v' <- gensym "tailprim"
                 let e' = LetE (v',[],SymDictTy (Just a) $ stripTyLocs dty, PrimAppE (DictInsertP dty) [(VarE a),d,k,v]) (VarE v')
                 -- we fmap location at the top-level case expression
                 go (e')

          -- Same AppE as above. This could just fail, instead of trying to repair
          -- the program.
          PrimAppE pr es -> do
                 v' <- gensym "tailprim"
                 let ty = L1.primRetTy pr
                     e' = LetE (v',[],ty, PrimAppE pr es) (VarE v')
                 -- we fmap location at the top-level case expression
                 go (e')

          -- RouteEnds creates let bindings for such expressions (see those cases below).
          -- Processing the RHS here would cause an infinite loop.

          LetE (v,ls,ty@(PackedTy _ loc),e1@DataConE{}) e2 -> do
            e2' <- exp inst_waiting_on_loc fns retlocs eor (M.insert (fromVarToFreeVarsTy v) loc lenv) afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) e2
            return $ LetE (v,ls,ty,e1) e2'

          LetE (v,ls,ty@(PackedTy _ loc),e1@(PrimAppE (ReadPackedFile{}) [])) e2 -> do
            e2' <- exp inst_waiting_on_loc fns retlocs eor (M.insert (fromVarToFreeVarsTy v) loc lenv) afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) e2
            return $ LetE (v,ls,ty,e1) e2'

          LetE (v,ls,ty,e1@ProjE{}) e2 -> do
            let lenv' = case ty of
                          PackedTy _ loc -> M.insert (fromVarToFreeVarsTy v) loc lenv
                          _ -> lenv
            e2' <- exp inst_waiting_on_loc fns retlocs eor lenv' afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) e2
            return $ LetE (v,ls,ty,e1) e2'

          LetE (v,ls,ty,e1@MkProdE{}) e2 -> do
            LetE (v,ls,ty,e1) <$> exp inst_waiting_on_loc fns retlocs eor lenv afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) e2

          LetE (v,ls,ty,e1@(PrimAppE (DictLookupP _) _)) e2 -> do
            LetE (v,ls,ty,e1) <$> exp inst_waiting_on_loc fns retlocs eor lenv afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) e2

          --

          LetE (v,ls,ty@(PackedTy n l),e1) e2 -> do
                 e1' <- go e1
                 e2' <- exp inst_waiting_on_loc fns retlocs eor (M.insert (fromVarToFreeVarsTy v) l lenv) afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) e2
                 return $ LetE (v,ls,PackedTy n l,e1') e2'

          LetE (v,ls,ty,e1@TimeIt{}) e2 -> do
                 e1' <- go e1
                 e2' <- exp inst_waiting_on_loc fns retlocs eor lenv afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) e2
                 return $ LetE (v,ls,ty,e1') e2'

          -- Most boring LetE case, just recur on body
          LetE (v,ls,ty,rhs) bod -> do
            bod' <- exp inst_waiting_on_loc fns retlocs eor lenv afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) bod
            return $ LetE (v,ls,ty,rhs) bod'

          IfE e1 e2 e3 -> do
                 e2' <- go e2
                 e3' <- go e3
                 return $ IfE e1 e2' e3'

          MkProdE ls -> do
            let tys = L.map (gRecoverTypeLoc ddefs env2) ls
                prodty = ProdTy tys
            v <- gensym "flt_RE"
            let ex = L1.mkLets [(v,[],prodty,(MkProdE ls))] (VarE v)
            exp inst_waiting_on_loc fns retlocs eor lenv afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) prodty env2) ex

          ProjE{} -> do
            v <- gensym "flt_RE"
            let ty = gRecoverTypeLoc ddefs env2 e
                lenv' = case ty of
                          PackedTy _ loc -> M.insert (fromVarToFreeVarsTy v) loc lenv
                          _ -> lenv
                ex = L1.mkLets [(v,[],ty,e)] (VarE v)
            exp inst_waiting_on_loc fns retlocs eor lenv' afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v) ty env2) ex

          -- Could fail here, but try to fix the broken program
          DataConE loc dc es -> do
                 v' <- gensym "taildc"
                 let ty = PackedTy (getTyOfDataCon ddefs dc) loc
                     e' = LetE (v',[],ty, DataConE loc dc es)
                               (VarE v')
                 exp inst_waiting_on_loc fns retlocs eor (M.insert (fromVarToFreeVarsTy v') loc lenv) afterenv (extendVEnvLocVar (fromVarToFreeVarsTy v') ty env2) (e')

          LitE i -> return (LitE i)
          CharE i -> return (CharE i)
          FloatE i -> return (FloatE i)

          LitSymE v -> return $ LitSymE v

          TimeIt e ty b -> do
                 e' <- go e
                 return $ TimeIt e' ty b

          WithArenaE v e -> WithArenaE v <$> go e

          Ext (LetRegionE r sz ty e) -> do
            e' <- go e
            return $ Ext (LetRegionE r sz ty e')

          Ext (LetParRegionE r sz ty e) -> do
            e' <- go e
            return $ Ext (LetParRegionE r sz ty e')

          Ext (LetLocE v locexp bod) -> do
            let only_recur e = do
                  e' <- go e
                  return $ Ext (LetLocE v locexp e')
            case locexp of
              StartOfRegionLE{} -> only_recur bod
              AfterConstantLE{} -> only_recur bod
              AfterVariableLE{} -> only_recur bod
              InRegionLE{} -> only_recur bod
              FreeLE{} -> only_recur bod
              FromEndLE{} -> only_recur bod
              GetDataConLocSoA{} -> only_recur bod 
              GetFieldLocSoA{} -> only_recur bod
              GenSoALoc{} -> only_recur bod
              _ -> error $ "RouteEnds: todo" ++ sdoc e

          Ext (L2.StartOfPkdCursor{})-> pure e

          Ext (IndirectionE{}) -> return e

          Ext (LetAvail vs e)  -> Ext <$> LetAvail vs <$> go e

          Ext ext -> error $ "RouteEnds: Shouldn't encounter " ++ sdoc ext

          MapE{} -> error "RouteEnds: todo MapE"
          FoldE{} -> error "RouteEnds: todo FoldE"

        where  mkRet :: [LocVar] -> Exp2 -> PassM Exp2
               mkRet ls (VarE v) =
                 let ends = L.map (\l -> findEnd l eor) ls
                 in return $ Ext (RetE ends v)
               mkRet _ e = error $ "Expected variable reference in tail call, got "
                           ++ (show e)

               funtype :: Var -> ArrowTy2 Ty2
               funtype v = case M.lookup v fns of
                             Nothing -> error $ "Function " ++ (show v) ++ " not found"
                             Just fundef -> funTy fundef

               go = exp inst_waiting_on_loc fns retlocs eor lenv afterenv env2


               -- We may need to emit some additional let bindings if we've reached
               -- an end witness that is equivalent to the after location of something.
               wrapBody f e ((l1,l2):ls) inst_waiting_on_loc =
                 case M.lookup (fromLocVarToFreeVarsTy l1) afterenv of
                   Nothing -> let let_to_release = case (M.lookup l1 inst_waiting_on_loc) of
                                                                Just lets -> lets
                                                                Nothing -> [] 
                                  inst_waiting_on_loc' = M.delete l1 inst_waiting_on_loc
                                  (e'', inst_waiting_on_loc'', let_to_release') = wrapBody f e ls inst_waiting_on_loc' 
                                in (e'', inst_waiting_on_loc'', let_to_release ++ let_to_release') 
                   Just la ->
                     let go loc acc =
                           case M.lookup (fromLocVarToFreeVarsTy loc) (vEnv env2) of
                             Just ty
                               | isScalarTy ty ->
                                 case M.lookup (fromLocVarToFreeVarsTy loc) afterenv of
                                   Nothing -> acc
                                   Just lb -> go lb (acc ++ [(lb,loc,fromJust $ sizeOfTy ty)])
                               | otherwise -> acc
                             Nothing -> acc
                         scalar_witnesses = go la []
                         bind_witnesses bod ls =
                           L.foldr (\(v,w,sz) acc ->
                                     Ext $ LetLocE v (AfterConstantLE sz w) acc)
                           bod ls
                         bod' = bind_witnesses e scalar_witnesses
                         --l2' = case l2 of
                         --          L l2loc -> l2loc 
                         --          _ -> error "RouteEnds: wrapBody: expected location."
                         -- VS: Here we need to check the type of location. 
                         -- it is possible that we have a complex after location, an SoA one. 
                         -- We might need to assign its parts appropriately.
                        --  bod'' =  Ext (LetLocE la (FromEndLE l2) bod')
                        --   in wrapBody f bod'' ls
                        in if True -- ( isSubset "print" (show f))
                         then
                          let (bod'', inst_waiting_on_loc', rels)  = case la of
                                    Single _ -> (Ext (LetLocE la (FromEndLE l2) bod'), inst_waiting_on_loc, [])
                                    SoA dloc flocs -> case M.lookup (fromLocVarToFreeVarsTy la) (vEnv env2) of
                                                                  Just ty -> case ty of 
                                                                                PackedTy tycon _ -> case M.lookup (fromLocVarToFreeVarsTy l1) (vEnv env2) of 
                                                                                                                  Just ty' -> case ty' of
                                                                                                                                PackedTy tycon' _ -> if tycon == tycon'
                                                                                                                                                     then 
                                                                                                                                                      let 
                                                                                                                                                        let_to_release = case (M.lookup l1 inst_waiting_on_loc) of
                                                                                                                                                                                            Just lets -> lets
                                                                                                                                                                                            Nothing -> []
                                                                                                                                                        in (Ext (LetLocE la (FromEndLE l2) bod'), inst_waiting_on_loc, let_to_release)
                                                                                                                                                     else
                                                                                                                                                       let same_ty_loc = findSubSetLoc la l2
                                                                                                                                                         in case same_ty_loc of 
                                                                                                                                                                Nothing -> error $ "RouteEnds: could not find same loc for: " ++ show (l2, la)
                                                                                                                                                                Just l2loc -> let  
                                                                                                                                                                    alias_same = [LetLocE l2loc (FromEndLE l2)]
                                                                                                                                                                    gen_soa = GenSoALoc (getDconLoc la) flocs 
                                                                                                                                                                    let_soa = [LetLocE la gen_soa]
                                                                                                                                                                    let_soa_data = [LetLocExpr la gen_soa]
                                                                                                                                                                    let_to_release = case (M.lookup l1 inst_waiting_on_loc) of
                                                                                                                                                                                            Just lets -> let lets' = L.map (\exp -> case exp of 
                                                                                                                                                                                                                                          LetLocExpr a b -> LetLocE a b
                                                                                                                                                                                                                          ) lets
                                                                                                                                                                                            
                                                                                                                                                                                                           in lets' ++ alias_same
                                                                                                                                                                                            Nothing -> alias_same
                                                                                                                                                                    inst_waiting_on_loc' = M.delete l1 inst_waiting_on_loc 
                                                                                                                                                                    inst_waiting_on_loc'' = case (M.member la inst_waiting_on_loc) of
                                                                                                                                                                                            True -> M.adjust (\vals -> vals ++ let_soa_data) la inst_waiting_on_loc'
                                                                                                                                                                                            False -> M.insert la let_soa_data inst_waiting_on_loc'
                                                                                                                                                                    bod'' = L.foldr (\lete acc -> Ext $ lete acc) bod' let_to_release
                                                                                                                                                                   in (bod'', inst_waiting_on_loc'', [])



                                                                                                                                _ -> (Ext (LetLocE la (FromEndLE l2) bod'), inst_waiting_on_loc, [])
                                                                                                                  Nothing -> (Ext (LetLocE la (FromEndLE l2) bod'), inst_waiting_on_loc, [])
                                                                                _ -> (Ext (LetLocE la (FromEndLE l2) bod'), inst_waiting_on_loc, [])
                                                                  Nothing -> (Ext (LetLocE la (FromEndLE l2) bod'), inst_waiting_on_loc, [])
                              (bod''', inst_waiting_on_loc'', rel) = wrapBody f bod'' ls inst_waiting_on_loc'       
                            in (bod''', M.unionWith (++) inst_waiting_on_loc' inst_waiting_on_loc'', rels ++ rel)
                         else
                          let bod'' = Ext (LetLocE la (FromEndLE l2) bod')
                              (bod''', inst_waiting_on_loc', rel) = wrapBody f bod'' ls inst_waiting_on_loc 
                            in (bod''', M.unionWith (++) inst_waiting_on_loc' inst_waiting_on_loc, rel)
               wrapBody f e [] inst_waiting_on_loc = (e, inst_waiting_on_loc, [])

               -- Process a let bound fn app.
               doBoundApp :: Var -> [LocVar] -> PassM ([LocVar], [(LocVar, LocVar)], EndOfRel)
               doBoundApp f lsin = do
                 let fty = funtype f
                     rets = S.fromList $ locRets fty
                     -- The travlist is a list of pair (location, bool) where the bool is
                     -- if the location was traversed, and the location is from the
                     -- AppE call.
                     travlist = zip lsin $ L.map (\l -> S.member (EndOf l) rets)  (locVars fty)

                 -- For each traversed location, gensym a new variable for its end,
                 -- and generate a list of (location, endof location) pairs.
                 let handleTravList lst (_l,False) = return lst
                     handleTravList lst (l,True) = (freshCommonLoc "endof" l) >>= \l' -> return $ (l, l'):lst

                 -- Walk through our pairs of (location, endof location) and update the
                 -- endof relation.
                 let mkEor (l1,l2) eor = mkEnd l1 l2 eor


                 newls <- reverse <$> foldM handleTravList [] travlist
                 let eor' = L.foldr mkEor eor newls
                 let outlocs = L.map snd newls
                 dbgTrace (minChatLvl) "Print in doBoundApp: " dbgTrace (minChatLvl) (sdoc (f, newls)) dbgTrace (minChatLvl) "End in doBoundAppE.\n" return (outlocs, newls, eor')


isSubset :: String -> String -> Bool
isSubset subset str = all (`elem` str) (L.nub subset)

findSubSetLoc :: LocVar -> LocVar -> Maybe LocVar
findSubSetLoc l1@(SoA dloc1 flocs1) l2@(SoA dloc2 flocs2) = if l1 == l2 then Just l1
                                                            else checkIfFieldLocInLoc flocs1 l2
findSubSetLoc l1@(SoA dloc1 flocs1) l2@(Single dloc2) = Nothing
findSubSetLoc l1@(Single _) l2@(SoA _ _) = Nothing
findSubSetLoc l1@(Single dloc1) l2@(Single dloc2) = if l1 == l2 then Just l1
                                                      else Nothing



checkIfFieldLocInLoc :: [((DataCon, Int), LocVar)] -> LocVar -> Maybe LocVar
checkIfFieldLocInLoc f1 f2 = let ret = L.foldr (\(_, f1') acc -> case f1' of
                                                              SoA _ floc1 -> case f2 of
                                                                     SoA _ floc2 -> if ((L.length floc1) == (L.length floc2)) && (ensureFieldsSameSoALoc floc1 floc2)
                                                                                    then Just f1'
                                                                                    else acc
                                                                     Single _ -> acc
                                                              Single _ -> case f2 of
                                                                      SoA _ floc2 -> acc
                                                                      Single _ -> if f1' == f2
                                                                                  then Just f1'
                                                                                  else acc
                                              ) Nothing f1
                              in ret

ensureFieldsSameSoALoc :: [((DataCon, Int), LocVar)] -> [((DataCon, Int), LocVar)] -> Bool
ensureFieldsSameSoALoc [] [] = True
ensureFieldsSameSoALoc l1 l2 = let l1' = L.map (\(k, _) -> k) l1
                                   l2' = L.map (\(k, _) -> k) l2
                               in if l1' == l2'
                                  then True
                                  else False