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

import Data.List as L
import Data.Loc
import Data.Map as M
import Data.Set as S
import Control.Monad

import Gibbon.Common
import Gibbon.L2.Syntax as L2
import Gibbon.L1.Syntax as L1


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
      env2 = progToEnv prg
  -- Handle the main expression (if it exists):
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (e,t) -> do e' <- exp fundefs'' [] emptyRel M.empty M.empty env2 e
                                 return $ Just (e',t)

  -- Return the updated Prog
  return $ Prog ddefs fundefs'' mainExp'


  where
    -- Helper functions:

    -- | Process function types (but don't handle bodies)
    fdty :: L2.FunDef2 -> PassM L2.FunDef2
    fdty FunDef{funName,funTy,funArgs,funBody} =
        do let (ArrowTy2 locin tyin eff tyout _locout) = funTy
               handleLoc (LRM l r m) ls = if S.member (Traverse l) eff then (LRM l r m):ls else ls
               locout' = L.map EndOf $ L.foldr handleLoc [] locin
           return FunDef{funName,funTy=(ArrowTy2 locin tyin eff tyout locout'),funArgs,funBody}


    -- | Process function bodies
    fd :: FunDefs2 -> L2.FunDef2 -> PassM L2.FunDef2
    fd fns FunDef{funName,funTy,funArgs,funBody} =
        do let (ArrowTy2 locin tyins eff _tyout _locout) = funTy
               handleLoc (LRM l _r _m) ls = if S.member (Traverse l) eff then l:ls else ls
               retlocs = L.foldr handleLoc [] locin
               lenv = L.foldr
                        (\(a,t) acc -> case t of
                                         PackedTy _ loc -> M.insert a loc acc
                                         _ -> acc)
                        M.empty (zip funArgs tyins)
               initVEnv = M.fromList $ zip funArgs tyins
               env2 = Env2 initVEnv (initFunEnv fundefs)
           funBody' <- exp fns retlocs emptyRel lenv M.empty env2 funBody
           return FunDef{funName,funTy,funArgs,funBody=funBody'}


    -- | Process expressions.
    -- Takes the following arguments:
    -- 1. a function environment
    -- 2. a list of locations we need to return the ends of
    -- 3. an end-of relation
    -- 4. a map of var to location
    -- 5. a map from location to location after it
    -- 6. the expression to process
    exp :: FunDefs2 -> [LocVar] -> EndOfRel -> M.Map Var LocVar ->
           M.Map LocVar LocVar -> Env2 Ty2 -> L Exp2 -> PassM (L Exp2)
    exp fns retlocs eor lenv afterenv env2 (L p e) = fmap (L p) $
        case e of

          -- Variable case, *should* be the base case assuming our expression was
          -- properly put in ANF.
          -- We generate our RetE form here. By this point we should know the ends
          -- of each of the locactions in relocs.

          -- we fmap location at the top-level case expression
          VarE v -> fmap unLoc $ mkRet retlocs $ l$ VarE v


          -- If a function has a literal as it's tail, it cannot return any
          -- end witnesses (since only VarE forms are converted to RetE's).
          -- We therefore bind that literal to a variable, and recur. We need
          -- to handle LetRegionE and LetLocE similarly.
          LetE (v,ls,ty,rhs) (L _ (LitE n)) -> do
            tmp <- gensym "fltLitTail"
            let e = l$ LetE (v,ls,ty,rhs) (l$ LetE (tmp,[],IntTy,l$ LitE n) (l$ VarE tmp))
            unLoc <$> exp fns retlocs eor lenv afterenv env2 e

          -- This is the most interesting case: a let bound function application.
          -- We need to update the let binding's extra location binding list with
          -- the end witnesses returned from the function.
          LetE (v,_ls,ty,rhs@(L _ (AppE f lsin e1))) e2 -> do
                 let lenv' = case ty of
                               PackedTy _n l -> M.insert v l lenv
                               _ -> lenv

                 (outlocs,newls,eor') <- doBoundApp rhs
                 e2' <- exp fns retlocs eor' lenv' afterenv (extendVEnv v ty env2) e2
                 return $ LetE (v,outlocs,ty, l$ AppE f lsin e1)
                               (wrapBody e2' newls)

          --
          LetE (v,_ls,ty, rhs@(L _ (ParE a b))) bod -> do
            (outlocs1,newls1,eor1) <- doBoundApp a
            (outlocs2,newls2,eor2) <- doBoundApp b
            let eor' = eor1 <> eor2
                newls' = newls1 <> newls2
                outlocs' = outlocs1 <> outlocs2
                -- TODO: How to handle tuples in lenv ?
                -- lenv' = if hasPacked ty
                --         then M.insert v (locsInTy ty) lenv
                --         else lenv
            bod' <- exp fns retlocs eor' lenv afterenv (extendVEnv v ty env2) bod
            return $ LetE (v,outlocs',ty,rhs)
                          (wrapBody bod' newls')

          CaseE (L _ (VarE x)) brs -> do
                 -- We will need to gensym while processing the case clauses, so
                 -- it has to be in the PassM monad
                 brs' <-
                     forM brs $ \(dc, vls, e) ->
                       case vls of
                         [] ->
                           case (M.lookup x lenv) of
                             Just l1 -> do
                               l2 <- gensym "jump"
                               let eor' = mkEnd l1 l2 eor
                                   e' = l$ Ext $ LetLocE l2 (AfterConstantLE 1 l1) e
                               e'' <- exp fns retlocs eor' lenv (M.insert l1 l2 lenv) env2 e'
                               return (dc, vls, e'')
                             Nothing -> error $ "Failed to find " ++ sdoc x
                         _ -> do
                           let need = snd $ last vls
                               argtys = lookupDataCon ddefs dc
                               lx = case M.lookup x lenv of
                                      Nothing -> error $ "Failed to find " ++ (show x)
                                      Just l -> l
                               -- we know lx and need have the same end, since
                               -- lx is the whole packed thing and need is its
                               -- last field, so when we look up the end of lx
                               -- what we really want is the end of need.
                               eor' = mkEqual lx need eor
                               f (l1,l2) env = M.insert l1 l2 env
                               afterenv' = L.foldr f afterenv $ zip (L.map snd vls) (tail $ L.map snd vls)
                               -- two cases here for handing bound parameters:
                               -- we have a packed type:
                               handleLoc (eor,e) (_,(PackedTy _ _)) = return (eor,e)
                               -- or we have a non-packed type, and we need to "jump" over it and
                               -- bind a location to after it
                               handleLoc (eor,e) (l1,ty) = do
                                    l2 <- gensym "jump"
                                    let eor' = mkEnd l1 l2 eor
                                        (Just jump) = L1.sizeOfTy ty
                                        e' = Ext $ LetLocE l2 (AfterConstantLE jump l1) e
                                    return (eor', l$ e')

                               vars = L.map fst vls
                               env2' = extendsVEnv (M.fromList (zip vars argtys)) env2

                           (eor'',e') <- foldM handleLoc (eor',e) $ zip (L.map snd vls) argtys
                           e'' <- exp fns retlocs eor'' lenv afterenv' env2' e'
                           return (dc, vls, e'')
                 return $ CaseE (l$ VarE x) brs'



          CaseE complex brs -> do
            let ty = gRecoverType ddefs env2 complex
            v <- gensym "flt_RE"
            let ex = L1.mkLets [(v,[],ty,complex)] (l$ CaseE (l$ VarE v) brs)
            unLoc <$> exp fns retlocs eor lenv afterenv (extendVEnv v ty env2) ex

          -------------------------------------------------------------------------------------------------------------------------
          --- That's all the interesting cases. The rest are straightforward:


          -- This shouldn't happen, but as a convenience we can ANF-ify this AppE
          -- by gensyming a new variable, sticking the AppE in a LetE, and recuring.
          -- Question: should this fail instead? I'm not sure.
          AppE v args e -> do
                 v' <- gensym "tailapp"
                 let ty = funtype v
                     -- use locVars used at call-site in the type
                     arrOutMp = M.fromList $ zip (allLocVars ty) args
                     outT     = substLoc arrOutMp (arrOut ty)
                     e' = LetE (v',[], outT, l$ AppE v args e) (l$ VarE v')
                 -- we fmap location at the top-level case expression
                 fmap unLoc $ go (l$ e')

          -- Same as above. This could just fail, instead of trying to repair
          -- the program.
          PrimAppE pr es -> do
                 v' <- gensym "tailprim"
                 let ty = L1.primRetTy pr
                     e' = LetE (v',[],ty, l$ PrimAppE pr es) (l$ VarE v')
                 -- we fmap location at the top-level case expression
                 fmap unLoc $ go (l$ e')


          -- RouteEnds creates let bindings for such expressions (see those cases below).
          -- Processing the RHS here would cause an infinite loop.

          LetE (v,ls,ty@(PackedTy _ loc),e1@(L _ DataConE{})) e2 -> do
            e2' <- exp fns retlocs eor (M.insert v loc lenv) afterenv (extendVEnv v ty env2) e2
            return $ LetE (v,ls,ty,e1) e2'

          LetE (v,ls,ty@(PackedTy _ loc),e1@(L _ (PrimAppE (ReadPackedFile{}) []))) e2 -> do
            e2' <- exp fns retlocs eor (M.insert v loc lenv) afterenv (extendVEnv v ty env2) e2
            return $ LetE (v,ls,ty,e1) e2'

          LetE (v,ls,ty,e1@(L _ ProjE{})) e2 -> do
            let lenv' = case ty of
                          PackedTy _ loc -> M.insert v loc lenv
                          _ -> lenv
            e2' <- exp fns retlocs eor lenv' afterenv (extendVEnv v ty env2) e2
            return $ LetE (v,ls,ty,e1) e2'

          LetE (v,ls,ty,e1@(L _ MkProdE{})) e2 -> do
            LetE (v,ls,ty,e1) <$> go e2

          --

          LetE (v,ls,ty@(PackedTy n l),e1) e2 -> do
                 e1' <- go e1
                 e2' <- exp fns retlocs eor (M.insert v l lenv) afterenv (extendVEnv v ty env2) e2
                 return $ LetE (v,ls,PackedTy n l,e1') e2'

          LetE (v,ls,ty,e1@(L _ TimeIt{})) e2 -> do
                 e1' <- go e1
                 e2' <- exp fns retlocs eor lenv afterenv (extendVEnv v ty env2) e2
                 return $ LetE (v,ls,ty,e1') e2'

          -- Most boring LetE case, just recur on body
          LetE (v,ls,ty,e1) e2 -> do
                 e2' <- exp fns retlocs eor lenv afterenv (extendVEnv v ty env2) e2
                 return $ LetE (v,ls,ty,e1) e2'

          IfE e1 e2 e3 -> do
                 e2' <- go e2
                 e3' <- go e3
                 return $ IfE e1 e2' e3'

          MkProdE ls -> do
            let tys = L.map (gRecoverType ddefs env2) ls
                prodty = ProdTy tys
            v <- gensym "flt_RE"
            let ex = L1.mkLets [(v,[],prodty,(l$ MkProdE ls))] (l$ VarE v)
            unLoc <$> exp fns retlocs eor lenv afterenv (extendVEnv v prodty env2) ex

          ProjE{} -> do
            v <- gensym "flt_RE"
            let ty = gRecoverType ddefs env2 e
                lenv' = case ty of
                          PackedTy _ loc -> M.insert v loc lenv
                          _ -> lenv
                ex = L1.mkLets [(v,[],ty,l$ e)] (l$ VarE v)
            unLoc <$> exp fns retlocs eor lenv' afterenv (extendVEnv v ty env2) ex

          -- Could fail here, but try to fix the broken program
          DataConE loc dc es -> do
                 v' <- gensym "taildc"
                 let ty = PackedTy (getTyOfDataCon ddefs dc) loc
                     e' = LetE (v',[],ty, l$ DataConE loc dc es)
                               (l$ VarE v')
                 fmap unLoc $ exp fns retlocs eor (M.insert v' loc lenv) afterenv (extendVEnv v' ty env2) (l$ e')

          LitE i -> return (LitE i)

          LitSymE v -> return $ LitSymE v

          TimeIt e ty b -> do
                 e' <- go e
                 return $ TimeIt e' ty b

          ParE a b -> ParE <$> go a <*> go b

          Ext (LetRegionE r (L _ (LitE n))) -> do
                 tmp <- gensym "fltLitTail"
                 let e = l$ Ext (LetRegionE r (l$ LetE (tmp,[],IntTy,l$ LitE n) (l$ VarE tmp)))
                 unLoc <$> exp fns retlocs eor lenv afterenv env2 e

          Ext (LetRegionE r e) -> do
                 e' <- go e
                 return $ Ext (LetRegionE r e')

          Ext (LetLocE v rhs (L _ (LitE n))) -> do
                 tmp <- gensym "fltLitTail"
                 let e = l$ Ext (LetLocE v rhs (l$ LetE (tmp,[],IntTy,l$ LitE n) (l$ VarE tmp)))
                 unLoc <$> exp fns retlocs eor lenv afterenv env2 e

          Ext (LetLocE v (StartOfLE r) e) -> do
                 e' <- go e
                 return $ Ext (LetLocE v (StartOfLE r) e')

          Ext (LetLocE v (AfterConstantLE i l1) e) -> do
                 e' <- go e
                 return $ Ext (LetLocE v (AfterConstantLE i l1) e')

          Ext (LetLocE v (AfterVariableLE x l1) e) -> do
                 e' <- go e
                 return $ Ext (LetLocE v (AfterVariableLE x l1) e')

          Ext (LetLocE v (InRegionLE r) bod) -> do
                 bod' <- go bod
                 return $ Ext (LetLocE v (InRegionLE r) bod')

          Ext (IndirectionE{}) -> return e

          -- For some reason this pass goes into an infinite loop if this is uncommented:
                                  
          -- Ext (LetLocE v FreeLE e) -> do
          --        e' <- go e
          --        return $ Ext (LetLocE v FreeLE e')

          Ext ext -> error $ "RouteEnds: Shouldn't encounter " ++ sdoc ext

          MapE{} -> error "RouteEnds: todo MapE"
          FoldE{} -> error "RouteEnds: todo FoldE"

        where  mkRet :: [LocVar] -> (L Exp2) -> PassM (L Exp2)
               mkRet ls (L p (VarE v)) =
                 let ends = L.map (\l -> findEnd l eor) ls
                 in return $ L p $ Ext (RetE ends v)
               mkRet _ e = error $ "Expected variable reference in tail call, got "
                           ++ (show e)

               funtype :: Var -> ArrowTy2
               funtype v = case M.lookup v fns of
                             Nothing -> error $ "Function " ++ (show v) ++ " not found"
                             Just fundef -> funTy fundef

               go = exp fns retlocs eor lenv afterenv env2


               -- We may need to emit some additional let bindings if we've reached
               -- an end witness that is equivalent to the after location of something.
               wrapBody e ((l1,l2):ls) =
                 case M.lookup l1 afterenv of
                   Nothing -> wrapBody e ls
                   Just la -> wrapBody (l$ (Ext (LetLocE la (FromEndLE l2) e))) ls
               wrapBody e [] = e

               -- Process a let bound fn app.
               doBoundApp :: L Exp2 -> PassM ([LocVar], [(LocVar, Var)], EndOfRel)
               doBoundApp (L _ (AppE f lsin _e1)) = do
                 let fty = funtype f
                     rets = S.fromList $ locRets fty
                     -- The travlist is a list of pair (location, bool) where the bool is
                     -- if the location was traversed, and the location is from the
                     -- AppE call.
                     travlist = zip lsin $ L.map (\l -> S.member (EndOf l) rets)  (locVars fty)

                 -- For each traversed location, gensym a new variable for its end,
                 -- and generate a list of (location, endof location) pairs.
                 let handleTravList lst (_l,False) = return lst
                     handleTravList lst (l,True) = gensym "endof" >>= \l' -> return $ (l,l'):lst

                 -- Walk through our pairs of (location, endof location) and update the
                 -- endof relation.
                 let mkEor (l1,l2) eor = mkEnd l1 l2 eor


                 newls <- reverse <$> foldM handleTravList [] travlist
                 let eor' = L.foldr mkEor eor newls
                 let outlocs = L.map snd newls
                 return (outlocs, newls, eor')
               doBoundApp oth = error $ "RouteEnds.doBoundApp: Got " ++ sdoc oth
