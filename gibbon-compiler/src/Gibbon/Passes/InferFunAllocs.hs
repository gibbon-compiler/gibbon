-- | Infer which functions can trigger GC.

module Gibbon.Passes.InferFunAllocs
  ( inferFunAllocs ) where

import Data.Map as M
import Gibbon.Common
import Gibbon.L2.Syntax

--------------------------------------------------------------------------------

-- | Chatter level for this module:
lvl :: Int
lvl = 5

type FunEnv = TyEnv FunMeta

inferFunAllocs :: Prog2 -> PassM Prog2
inferFunAllocs prg@Prog{fundefs} = do
  let finalMetas = fixpoint 1 fundefs (M.map funMeta fundefs)
      funs = M.map (\fn@FunDef{funName} ->
                       fn { funMeta = finalMetas ! funName })
             fundefs
  return $ prg { fundefs = funs }
  where
    fixpoint :: Int -> FunDefs2 -> FunEnv -> FunEnv
    fixpoint iter funs fenv =
       let metas = M.map (inferFunDef fenv) funs
       in if fenv == metas
          then dbgTrace lvl ("\n<== Fixpoint completed after iteration "++show iter++" ==>") $ fenv
          else fixpoint (iter+1) funs metas

inferFunDef :: FunEnv -> FunDef2 -> FunMeta
inferFunDef fenv FunDef{funBody,funMeta} =
  funMeta { funCanTriggerGC = inferExp fenv funBody }

inferExp :: FunEnv -> Exp2 -> Bool
inferExp fenv expr =
  case expr of
    VarE{}    -> False
    LitE{}    -> False
    CharE{}   -> False
    FloatE{}  -> False
    LitSymE{} -> False
    AppE v _locs _e -> funCanTriggerGC (fenv # v)
    PrimAppE _ ls   -> any go ls
    LetE (_,_,_,rhs) bod -> go rhs || go bod
    IfE tst consq alt    -> go tst || go consq || go alt
    MkProdE ls           -> any go ls
    SpawnE v _locs _e    -> funCanTriggerGC (fenv # v)
    SyncE      -> False
    ProjE _n e -> go e
    CaseE e mp -> go e || any (\(_,_,rhs) -> go rhs) mp
    DataConE _loc _dcon es -> any go es
    TimeIt e _ _           -> go e
    WithArenaE _v e -> go e
    MapE{}  -> error "inferFunAllocs: MapE not handled."
    FoldE{} -> error "inferFunAllocs: FoldE not handled."
    Ext (LetRegionE{})     -> True
    Ext (LetParRegionE{})  -> True
    Ext (LetLocE _ _ rhs)  -> go rhs
    Ext (RetE _ _)         -> False
    Ext (FromEndE _ )      -> False
    Ext (IndirectionE{})   -> False
    Ext (BoundsCheck{})    -> _todo -- (S.empty, Nothing)
    Ext (AddFixed{})       -> False
    Ext (GetCilkWorkerNum) -> False
    Ext (LetAvail _ e)     -> go e
  where
    go = inferExp fenv
