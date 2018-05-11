{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- | A pass to route end-witnesses as additional function returns.
--
-- GRAMMAR: takes and produces a flattened L2 program.
-- Returns a program following the "end-witnesses" calling convention.
--
module Gibbon.Passes.RouteEnds
    ( routeEnds ) where

import           Gibbon.Common hiding (FunDef)
import qualified Gibbon.L1.Syntax as L1
import qualified Gibbon.L2.Syntax as L2

-- We use some pieces from this other attempt:
import           Gibbon.L2.Syntax as L2
import           Gibbon.Passes.InferEffects (instantiateApp, freshLoc)
import Data.List as L hiding (tail)
import Data.Map as M
import Data.Set as S
import Text.PrettyPrint.GenericPretty
import Control.Monad
import Control.Exception
import Prelude hiding (exp)

-- | Chatter level for this module:
lvl :: Int
lvl = 4


-- =============================================================================


-- | The goal of this pass is to take effect signatures and translate
-- them into extra arguments and returns.  This pass does not worry
-- about where the witnesses come from to synthesize these extra
-- returns, it just inserts references to them that create *demand*.
--
-- This pass introduces *witness variables*.  These are operationally
-- equivalent to the original variable, but they always have type
-- CursorTy, even though the original value they are witnessing has
-- not YET been turned into a cursor.  Thus, `witness_x = (CursorTy)x`.
--
routeEnds :: L2.Prog -> SyM L2.Prog
routeEnds L2.Prog{ddefs,fundefs,mainExp} = do
    fds' <- mapM fd $ M.elems fundefs

    mn <- case mainExp of
            Nothing -> return Nothing
            Just (x,t)  -> do (x',_) <- exp [] M.empty x
                              return $ Just (x',t)
                -- do let initWenv = WE (M.singleton gloc (L1.VarE "gcurs")) M.empty
                --    tl' <- tail [] (M.empty,initWenv) x
                --    return $ Just $ L1.LetE ("gcurs", CursorTy, NewBuffer) tl'
    return L2.Prog{ fundefs = M.fromList $ L.map (\f -> (L2.funname f,f)) fds'
                  , ddefs = ddefs
                  , mainExp = mn
                  }
 where

  fd :: L2.FunDef -> SyM L2.FunDef
  fd (f@L2.FunDef{funname,funty,funarg,funbod}) =
      let ArrowTy oldInT _effs _ = funty
          (newTy@(ArrowTy inT _ _),newOut) = cursorizeUrTy funty
      in
      dbgTrace lvl ("Processing fundef: "++show(doc f)++
                    "\n  new type: "++sdoc newTy++"\n  newOut: " ++ show (newOut)) $
   do
      -- First off, we need to use the lexical variable name to name
      -- the input's fixed abstract location (from the lambda body's prspective).
      let argLoc  = argtyToLoc (L2.mangle funarg) oldInT

--          localizedEffects  = substEffs (zipLT argLoc inT) effs
--          localizedEffects2 = substEffs (zipTL inT argLoc) effs

      -- We use the new type to determine the NEW return values:
      (_efs, retlocs) <- instantiateApp newTy argLoc
      let augments = if L.null newOut
                     then []
                     else case retlocs of
                            TupLoc l -> L.init l
                            _ -> error$ "routeEnds: expected a tuple return location: "++show retlocs
      let env0 =
           dbgTrace lvl (" !!! argLoc "++show argLoc++", inTy "++show inT++", instantiate: "++show retlocs) $
--           dbgTrace lvl (" !!! localEffs1 "++show localizedEffects++" locEffs2 "++show localizedEffects2) $
           M.singleton newArg argLoc
          newArg = funarg
          bod = funbod
          demand = L.map ((\(Just x) -> x) . getLocVar) augments -- newOut
      (exp',_) <- exp demand env0 bod
      return $ L2.FunDef funname newTy newArg exp'


  funType f = funty $ fundefs # f

  triv :: L1.Exp -> L1.Exp
  triv tr =
   case tr of
     VarE _                 -> tr -- Think about witness/end marking here.
     LitE _                 -> tr
     LitSymE _              -> tr
     PrimAppE L1.MkTrue  [] -> tr
     PrimAppE L1.MkFalse [] -> tr
     MkProdE ls             -> MkProdE $ L.map triv ls
     ProjE ix e             -> ProjE ix $ triv e

     _ -> error$ " [routeEnds] trivial expected: "++sdoc tr

  -- | Arguments:
  --
  --  (1) the N demanded traversal witnesses (end-of-input cursors)
  --  (2) an environment mapping lexical variables to abstract locations
  --  (3) expression to process
  --
  -- Return values:
  --
  --  (1) The updated expression, possibly with a tupled return type
  --      thereby including the N new cursor returns.
  --  (2) The location of the processed expression, NOT including the
  --      added returns.
  exp :: [LocVar] -> LocEnv -> L1.Exp -> SyM (L1.Exp, Loc)
  exp demanded env ex =
    dbgTrace lvl ("\n [routeEnds] exp, demanding "++show demanded++": "++show ex++"\n  with env: "++show env) $
    let trivLoc (VarE v)  = env # v
        trivLoc (LitE _i) = Bottom
        trivLoc (LitSymE _v) = Bottom
        trivLoc (MkProdE ls) = TupLoc (L.map trivLoc ls)
        trivLoc (ProjE ix trv) =
            case trivLoc trv of
              TupLoc ls -> ls !! ix
              oth -> error $ "No way to describe a location projected from a tuple of this location: "++show oth

        trivLoc (PrimAppE L1.MkTrue [])  = Bottom
        trivLoc (PrimAppE L1.MkFalse []) = Bottom
        trivLoc t = error $ "Case in trivLoc not handled for: " ++ (show t)

        -- When we get to the end... we just mention the names of what we want:
        defaultReturn e = L1.mkProd $ (L.map VarE demanded) ++ [e]
    in
    case ex of
     -----------------Trivials---------------------
     -- ASSUMPTION we are ONLY given demands that we can FULFILL:

     tr | L1.isTriv tr -> return ( defaultReturn (triv tr)
                                 , trivLoc tr)
     ----------------End Trivials-------------------

     -- PrimApps do not currently produce end-witnesses:
     PrimAppE p ls -> L1.assertTrivs ls $
                       pure (defaultReturn (PrimAppE p (L.map triv ls)),Bottom)

     -- A datacon is the beginning of something new, it certainly
     -- cannot witness the end of anything else!
     DataConE k ls -> L1.assertTrivs ls $
       do fresh <- freshLoc "dunno"
          return (defaultReturn (DataConE k ls), fresh)

     -- Allocating new data doesn't witness the end of any data being read.
     LetE (v,ty, DataConE k ls) bod -> L1.assertTrivs ls $
       do env' <- extendLocEnv [(v,ty)] env
          (bod',loc) <- exp demanded env' bod
          return (LetE (v,ty,DataConE k ls) bod', loc)

     -- FIXME: Need unariser pass:
     LetE (vr,ty, MkProdE ls) bod -> L1.assertTrivs ls $ do
      -- As long as we keep these trivial, this is book-keeping only.  Nothing to route out of here.
      env' <- extendLocEnv [(vr,ty)] env
      (bod',loc) <- exp demanded env' bod
      return (LetE (vr,ty,MkProdE ls) bod', loc)

    -- A let is a fork in the road, a compound expression where we
    -- need to decide which branch can fulfill a given demand.
     LetE (v,t,rhs) bod ->
      do
         ((fulfilled,demanded'), rhs', _rloc) <- maybeFulfill demanded env rhs
         env' <- extendLocEnv [(v,t)] env
         (bod', bloc) <- exp demanded' env' bod
         let num1 = length fulfilled
             num2 = length demanded'
             newExp = LetE (v,t, L1.mkProj num1 (num1+1) rhs') bod'
         assert (num1 + num2 == length demanded) $
            return (newExp, bloc)

     --  We're allowing these as tail calls:
     AppE rat rand -> -- L1.assertTriv rnd $
       let loc = trivLoc rand in
          do
             -- This looks up the type before this pass, not with end cursors:
             let arrTy@(ArrowTy _ _ ouT) = funType rat
             (effs,loc) <- instantiateApp arrTy loc
             if L.null effs
              then dbgTrace lvl (" [routeEnds] processing app with ZERO extra end-witness returns:\n  "++sdoc ex) $
                   assert (demanded == []) $
                   return (AppE rat rand, loc) -- Nothing to see here.
              else do
                -- FIXME: THESE COULD BE IN THE WRONG ORDER:  (But it doesn't matter below.)
                let outs = L.map (\(Traverse v) -> toEndVar v) (S.toList effs)
                -- FIXME: assert that the demands match what we got back...
                -- might need to shuffle the order
                assert (length demanded == length outs) $! return ()
                let ouT' = L1.ProdTy $ (L.map mkCursorTy outs) ++ [ouT]
                tmp <- gensym $ toVar "hoistapp"
                let newExp = LetE (tmp, fmap (const ()) ouT', AppE rat rand) $
                               letBindProjections (L.map (\v -> (v,mkCursorTy ())) outs) (VarE tmp) $
                                 -- FIXME/TODO: unpack the witnesses we know about, returns 1-(N-1):
                                 (ProjE (length effs) (VarE tmp))
                dbgTrace lvl (" [routeEnds] processing app with these extra returns: "++
                                 show effs++", new expr:\n "++sdoc newExp) $!
                  return (defaultReturn newExp,loc)

     -- Here we must fulfill the demand on ALL branches uniformly.
     --
     -- FIXME: We will also need to create NEW DEMAND to witness the
     -- end of our non-first packed fields within the subexpressions
     -- of this case.  After copy insertion we know it is POSSIBLE,
     -- but we still need to figure out which subexpressions shoud be
     -- be demanded to produce them.
     CaseE e1 ls -> L1.assertTriv e1 $
      let scrutloc = let lp (VarE sv)     = env # sv
                         lp (ProjE ix e') = let TupLoc ls = lp e'
                                            in ls !!! ix
                         lp oth = error$ "[RouteEnds] FINISHME, handle case scrutinee at loc: "++show oth
                     in lp e1

          docase (dcon,patVs,rhs) = do
            let tys    = lookupDataCon ddefs dcon
                zipped = fragileZip patVs tys

            env' <- extendLocEnv zipped env
            (rhs',loc) <- exp demanded env' rhs

            -- Since this pass is the one concerned with End propogation,
            -- it's the one that reifies the fact "last field's end is constructors end".
            let rhs'' =
                  let Fixed v = scrutloc
                  in LetE (toEndVar v, mkCursorTy (),
                           case sequence (L.map L1.sizeOf tys) of
                             -- Here we statically know the layout, plus one for the tag:
                             Just ns -> AddCursor (L2.toWitnessVar v) (sum ns+1)
                             Nothing -> VarE (toEndVar (L.last patVs)))
                       rhs'

            return ((dcon,patVs,rhs''),loc)

      in do
            (ls',locs) <- unzip <$> mapM docase ls
            -- unless (1 == (length $ nub $ L.map L.length extras)) $
            --   error $ "Got inconsintent-length augmented-return types from branches of case:\n  "
            --           ++show extras++"\nExpr:\n  "++sdoc ex
            let (locFin,cnstrts) = joins locs

            when (not (L.null cnstrts)) $
             dbgTrace 1 ("Warning: routeEnds/FINISHME: process these constraints: "++show cnstrts) (return ())

            return (CaseE e1 ls', locFin)

     IfE a b c -> L1.assertTriv a $ do
       (b',bloc) <- exp demanded env b
       (c',cloc) <- exp demanded env c
       let (retloc,_) = L2.join bloc cloc
       return (IfE a b' c', retloc)

     TimeIt e t b -> do (e',l) <- exp demanded env e
                        return (TimeIt e' t b, l)

     _ -> error$ "[routeEnds] Unfinished.  Needs to handle:\n  "++sdoc ex
{-
      -- MapE (v,t,rhs) bod -> MapE <$> ((v,t,) <$> go rhs) <*> go bod
      -- FoldE (v1,t1,r1) (v2,t2,r2) bod ->
      --     FoldE <$> ((v1,t1,) <$> go r1)
      --           <*> ((v2,t2,) <$> go r2)
      --           <*> go bod
-}

  -- | Process an expression multiple times, first to see what it can
  -- offer, and then again if it can offer something we want.
  -- Returns hits followed by misses.
  maybeFulfill :: [LocVar] -> LocEnv -> L1.Exp -> SyM (([LocVar],[LocVar]),L1.Exp, Loc)
  maybeFulfill demand env ex = do
    (ex', loc) <- exp [] env ex
    let offered = locToEndVars loc
        matches = S.intersection (S.fromList demand) (S.fromList offered)

    if dbgTrace 2 ("[routeEnds] maybeFulfill, offered "++show offered
                   ++", demanded "++show demand++", from: "++show ex) $
       S.null matches
     then return (([],demand),ex',loc)
     else do
      let (hits,misses) = L.partition (`S.member` matches) demand
      (ex',loc) <- exp [] env ex
      return ((hits,misses), ex', loc)



locToEndVars :: Loc -> [Var]
locToEndVars l =
 case l of
   (Fixed x) | isEndVar x -> [x]
             | otherwise -> []
   (Fresh _) -> []
   (TupLoc ls) -> concatMap locToEndVars ls
   Top    -> []
   Bottom -> []


letBindProjections :: [(Var, L1.Ty)] -> Exp -> Exp -> Exp
letBindProjections ls tupname bod = go 0 ls
  where
    go _ [] = bod
    go ix ((vr,ty):rst) = LetE (vr, ty, ProjE ix tupname) $ go (ix+1) rst


-- | Let bind IFF there are extra cursor results.

-- maybeLetTup :: [Loc] -> (L1.Ty, L1.Exp) -> WitnessEnv
--             -> (L1.Exp -> WitnessEnv -> SyM L1.Exp) -> SyM L1.Exp
-- maybeLetTup locs (ty,ex) env fn = __refactor
{-maybeLetTup locs (ty,ex) env fn =
  case locs of
   -- []  -> error$ "maybeLetTup: didn't expect zero locs:\n  " ++sdoc (ty,ex)
   -- Zero extra cursor return values
   [] -> fn ex env
   -- Otherwise the layout of the tuple is (cursor0,..cursorn, origValue):
   _   -> do
     -- The name doesn't matter, just that it's in the environment:
     tmp <- gensym "mlt"
     -- Let-bind all the new things that come back with the exp
     -- to bring them into the environment.
     let env' = witnessBinding tmp (TupLoc locs) `unionWEnv` env
         n = length locs
     bod <- fn (mkProj (n - 1) n (L1.VarE tmp)) env'
     return $ L1.LetE (tmp, ty, ex) bod
-}

-- | A variable binding may be able to

-- varToWitnesses :: Var -> Loc -> M.Map LocVar Exp
-- varToWitnesses = __
{- varToWitnesses vr loc = WE (M.fromList $ go loc (L1.VarE vr)) M.empty
  where
   go (TupLoc ls) ex =
       concat [ go x (mkProj ix (length ls) ex)
              | (ix,x) <- zip [0..] ls ]
   go (Fresh v) e = [ (v,e) ]
   go (Fixed v) e = [ (v,e) ]
   go Top       _ = []
   go Bottom    _ = [] -}

-- data WitnessEnv -- WIP: REMOVE ME
