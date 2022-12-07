-- |  This is really a hack for benchmarking.
-- Lift global allocations outside of timing loop.s

-- WARNING: seeded with DUPLICATED code from Unariser

module Gibbon.Passes.HoistNewBuf
    (hoistNewBuf) where

import Prelude hiding (exp)
import qualified Data.List as L

import Gibbon.Common
import Gibbon.L3.Syntax


-- | Strip out the NewBuf bindings up until the point control flow diverges.
hoistNewBuf :: Prog3 -> PassM Prog3
hoistNewBuf = mapMExprs hoistExp

hoistExp :: ignored -> Exp3 -> PassM Exp3
hoistExp _ ex0 = return $ gocap ex0
  where

  gocap ex =
    if not (hasTimeIt ex) then ex else
      let (lets,ex') = go ex in
        mkLets lets ex'

  go :: Exp3 -> ([(Var,[()],Ty3,Exp3)], Exp3)
  go e0 =
   case e0 of
    (LitE _)      -> ([], e0)
    (CharE _)     -> ([], e0)
    (FloatE _)    -> ([], e0)
    (LitSymE _)   -> ([], e0)
    (VarE _)      -> ([], e0)
    (AppE _ _ _)  -> ([], e0)
    (PrimAppE{})  -> ([], e0)
    (MapE _ _)    -> error "hoistExp.go: FINISHME MapE"
    (FoldE _ _ _) -> error "hoistExp.go: FINISHME FoldE"

    -- Here's where we lift outside timings!!
    (TimeIt e t b) -> let (lts,e') = go e in
                      (lts, TimeIt e' t b)

    (LetE (v,locs,t, nb@((Ext NewBuffer{}))) bod) ->
        let (lts1,bod') = go bod in
        ((v,locs,t, nb):lts1, bod')

    (LetE (v,locs,t, nb@((Ext NewParBuffer{}))) bod) ->
        let (lts1,bod') = go bod in
        ((v,locs,t, nb):lts1, bod')

    (LetE (v,locs,t, nb@(Ext EndOfBuffer{}))
       bod) ->
        let (lts1,bod') = go bod in
        ((v,locs,t, nb):lts1, bod')

    -- boilerplate
    (LetE (v,locs,t,rhs) bod) ->
        let (lts1, rhs') = go rhs
            (lts2, bod') = go bod
        in (lts1++lts2, LetE (v,locs,t,rhs') bod')

    (IfE e1 e2 e3) ->
         let (lts1, e1') = go e1 in
         (lts1, IfE e1' (gocap e2) (gocap e3))

    (ProjE i e)  -> let (lts,e') = go e in
                    (lts, ProjE i e')
    (MkProdE es) -> let (ltss,es') = unzip $ L.map go es in
                    (concat ltss, MkProdE es')

    (CaseE scrt ls) -> let (lts,scrt') = go scrt
                       in (lts, CaseE scrt' [ (k,vs, gocap e)
                                            | (k,vs,e) <- ls ])
    (DataConE c loc es) -> let (ltss,es') = unzip $ L.map go es in
                           (concat ltss, DataConE c loc es')

    (SpawnE{})    -> ([], e0)

    (SyncE)       -> ([], e0)

    (WithArenaE v e) -> let (lts,e') = go e in
                        (lts, WithArenaE v e')

    (Ext _) -> ([], e0)


    -- (MapE (v,t,e') e) ->
    -- (FoldE (v1,t1,e1) (v2,t2,e2) e3) ->
