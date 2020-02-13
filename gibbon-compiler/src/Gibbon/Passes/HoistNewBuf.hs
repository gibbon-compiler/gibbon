-- |  This is really a hack for benchmarking.
-- Lift global allocations outside of timing loop.s

-- WARNING: seeded with DUPLICATED code from Unariser

module Gibbon.Passes.HoistNewBuf
    (hoistNewBuf) where

import Data.Loc
import Prelude hiding (exp)
import qualified Data.List as L

import Gibbon.Common
import Gibbon.L3.Syntax


-- | Strip out the NewBuf bindings up until the point control flow diverges.
hoistNewBuf :: Prog3 -> PassM Prog3
hoistNewBuf = mapMExprs hoistExp

hoistExp :: ignored -> L Exp3 -> PassM (L Exp3)
hoistExp _ ex0 = return $ gocap ex0
  where

  gocap ex = let (lets,ex') = go ex in
             mkLets lets ex'

  go :: L Exp3 -> ([(Var,[()],Ty3,L Exp3)], L Exp3)
  go (L p e0) = (\(x,y) -> (x, L p y)) $
   case e0 of
    (LitE _)      -> ([], e0)
    (LitSymE _)   -> ([], e0)
    (VarE _)      -> ([], e0)
    (AppE _ _ _)  -> ([], e0)
    (PrimAppE{})  -> ([], e0)
    (MapE _ _)    -> error "hoistExp.go: FINISHME MapE"
    (FoldE _ _ _) -> error "hoistExp.go: FINISHME FoldE"

    -- Here's where we lift outside timings!!
    (TimeIt e t b) -> let (lts,e') = go e in
                      (lts, TimeIt e' t b)

    (LetE (v,locs,t, nb@(L _ (Ext NewBuffer{}))) bod) ->
        let (lts1,bod') = go bod in
        ((v,locs,t, nb):lts1, unLoc bod')

    (LetE (v,locs,t, nb@(L _ (Ext (AddCursor _ (L _ (Ext (InitSizeOfBuffer{})))))))
       bod) ->
        let (lts1,bod') = go bod in
        ((v,locs,t, nb):lts1, unLoc bod')

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

    (IsBigE{}) -> ([], e0)

    -- (MapE (v,t,e') e) ->
    -- (FoldE (v1,t1,e1) (v2,t2,e2) e3) ->
