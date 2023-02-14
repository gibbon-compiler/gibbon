-- |  This is really a hack for benchmarking.
-- Lift global allocations outside of timing loop.s

-- WARNING: seeded with DUPLICATED code from Unariser

module Gibbon.Passes.HoistNewBuf
    (hoistNewBuf) where

import Prelude hiding (exp)
import qualified Data.List as L

import Gibbon.Common
import Gibbon.L3.Syntax

--------------------------------------------------------------------------------

data GcPoint = App | RegAlloc

-- | Strip out the NewBuf bindings up until the point control flow diverges.
hoistNewBuf :: Prog3 -> PassM Prog3
hoistNewBuf = mapMExprs hoistExp

hoistExp :: ignored -> Exp3 -> PassM Exp3
hoistExp _ ex0 = return $ gocap False ex0
  where
  -- Returns bindings from shadowstack pushes to pops, including the
  -- region allocation or function call.
  --
  -- assumption: let bindings for shadowstack push and pop ops, and the region
  -- allocation or function call appear one after the other, perhaps with code
  -- that can be hoisted in between.
  fromPushToPop :: (Var,[()],Ty3,Exp3) -> Exp3 -> ([(Var,[()],Ty3,Exp3)], GcPoint, Exp3)
  fromPushToPop first_push e0 =
    let
        pushes :: [(Var,[()],Ty3,Exp3)] -> Int -> GcPoint -> Exp3
               -> ([(Var,[()],Ty3,Exp3)], GcPoint, Exp3)
        pushes binds n mb_hoist e1 =
          case e1 of
            LetE b@(_v,_locs,_ty,rhs) bod ->
              case rhs of
                Ext(SSPush{})        -> pushes (binds ++ [b]) (n+1) mb_hoist bod
                Ext(SSPop{})         -> pops (binds ++ [b]) (n-1) mb_hoist bod
                Ext(NewBuffer{})     -> pushes (binds ++ [b]) n RegAlloc bod
                Ext(NewParBuffer{})  -> pushes (binds ++ [b]) n RegAlloc bod
                _                    -> pushes (binds ++ [b]) n mb_hoist bod
            _ -> error $ "hoistNewBuf: " ++ sdoc e1

        pops :: [(Var,[()],Ty3,Exp3)] -> Int -> GcPoint -> Exp3
             -> ([(Var,[()],Ty3,Exp3)], GcPoint, Exp3)
        pops binds 0 mb_hoist e1 = (binds, mb_hoist, e1)
        pops binds n mb_hoist e1 =
          case e1 of
            LetE b@(_v,_locs,_ty,rhs) bod ->
              case rhs of
                Ext(SSPop{}) -> pops (binds ++ [b]) (n-1) mb_hoist bod
                _ -> error $ "hoistNewBuf: expected pop, got " ++ sdoc rhs
            _ -> error $ "hoistNewBuf: " ++ sdoc e1
    in pushes [first_push] 1 App e0

  gocap hoist ex =
    if not (hasTimeIt ex) then ex else
      let (lets,ex') = go hoist ex in
        mkLets lets ex'

  go :: Bool -> Exp3 -> ([(Var,[()],Ty3,Exp3)], Exp3)
  go hoist e0 =
   case e0 of
    -- Here's where we lift outside timings!!

    (LetE bnd@(_v,_locs,_t,(Ext SSPush{})) bod) ->
      if hoist
        then
          let (binds, mb_hoist, cont) = fromPushToPop bnd bod
              (lts1,cont') = go hoist cont
          in case mb_hoist of
               RegAlloc -> (binds ++ lts1, cont')
               App      -> (lts1, mkLets binds cont')
        else let (lts, bod') = go hoist bod
             in (lts, LetE bnd bod')

    (LetE (v,locs,ty,(TimeIt e t b)) bod) ->
      let (lts, e') = go True e
          (lts1, bod') = go False bod
      in (lts ++ lts1, LetE (v,locs,ty,TimeIt e' t b) bod')

    (TimeIt e t b) -> let (lts,e') = go hoist e
                      in (lts, TimeIt e' t b)
    (LetE (v,locs,t, nb@((Ext NewBuffer{}))) bod) ->
      if hoist
      then let (lts1,bod') = go hoist bod
           in ((v,locs,t, nb):lts1, bod')
      else let (lts1,bod') = go hoist bod
           in  (lts1, LetE (v,locs,t,nb) bod')
    (LetE (v,locs,t, nb@((Ext NewParBuffer{}))) bod) ->
      if hoist
      then let (lts1,bod') = go hoist bod
           in ((v,locs,t, nb):lts1, bod')
      else let (lts1,bod') = go hoist bod
           in  (lts1, LetE (v,locs,t,nb) bod')
    (LetE (v,locs,t, nb@(Ext EndOfBuffer{})) bod) ->
      if hoist
      then let (lts1,bod') = go hoist bod
           in ((v,locs,t, nb):lts1, bod')
      else let (lts1,bod') = go hoist bod
           in  (lts1, LetE (v,locs,t,nb) bod')

    -- boilerplate

    (LitE _)      -> ([], e0)
    (CharE _)     -> ([], e0)
    (FloatE _)    -> ([], e0)
    (LitSymE _)   -> ([], e0)
    (VarE _)      -> ([], e0)
    (AppE _ _ _)  -> ([], e0)
    (PrimAppE{})  -> ([], e0)
    (MapE _ _)    -> error "hoistExp.go: FINISHME MapE"
    (FoldE _ _ _) -> error "hoistExp.go: FINISHME FoldE"

    (LetE (v,locs,t,rhs) bod) ->
        let (lts1, rhs') = go hoist rhs
            (lts2, bod') = go hoist bod
        in (lts1++lts2, LetE (v,locs,t,rhs') bod')

    (IfE e1 e2 e3) ->
         let (lts1, e1') = go hoist e1 in
         (lts1, IfE e1' (gocap hoist e2) (gocap hoist e3))

    (ProjE i e)  -> let (lts,e') = go hoist e in
                    (lts, ProjE i e')
    (MkProdE es) -> let (ltss,es') = unzip $ L.map (go hoist) es in
                    (concat ltss, MkProdE es')

    (CaseE scrt ls) -> let (lts,scrt') = go hoist scrt
                       in (lts, CaseE scrt' [ (k,vs, gocap hoist e)
                                            | (k,vs,e) <- ls ])
    (DataConE c loc es) -> let (ltss,es') = unzip $ L.map (go hoist) es in
                           (concat ltss, DataConE c loc es')

    (SpawnE{})    -> ([], e0)

    (SyncE)       -> ([], e0)

    (WithArenaE v e) -> let (lts,e') = go hoist e in
                        (lts, WithArenaE v e')

    (Ext _) -> ([], e0)


    -- (MapE (v,t,e') e) ->
    -- (FoldE (v1,t1,e1) (v2,t2,e2) e3) ->
