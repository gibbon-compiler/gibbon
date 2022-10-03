module Gibbon.Passes.TagRAN (tagRAN) where

import qualified Data.Map as M

import Gibbon.Common
import Gibbon.NewL2.Syntax as NewL2

--------------------------------------------------------------------------------

tagRAN :: Prog2 -> PassM Prog2
tagRAN Prog{ddefs,fundefs,mainExp} = do
  fds' <- mapM tagRANFn $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (mn, ty) -> Just <$> (,ty) <$> tagRANExp mn
  return $ Prog ddefs fundefs' mainExp'

tagRANFn :: FunDef2 -> PassM FunDef2
tagRANFn f@FunDef{funBody} = do
  funBody' <- tagRANExp funBody
  return $ f { funBody = funBody' }

tagRANExp :: Exp2 -> PassM Exp2
tagRANExp ex =
  case ex of
    Ext ext ->
      case ext of
        AddFixed{}     -> return ex
        StartOfPkd{}   -> return ex
        TagCursor{} -> return ex
        LetRegionE r sz ty bod    -> Ext <$> (LetRegionE r sz ty) <$> go bod
        LetParRegionE r sz ty bod -> Ext <$> (LetParRegionE r sz ty) <$> go bod
        LetLocE loc le bod        -> Ext <$> (LetLocE loc le) <$> go bod
        LetAvail vs e             -> Ext <$> (LetAvail vs) <$> go e
        RetE{}                -> return ex
        FromEndE{}            -> return ex
        BoundsCheck{}         -> return ex
        IndirectionE{}        -> return ex
        GetCilkWorkerNum      -> return ex
        AllocateTagHere{}     -> return ex
        AllocateScalarsHere{} -> return ex
        SSPush{}              -> return ex
        SSPop{}               -> return ex
    -- Straightforward recursion ...
    VarE{}     -> return ex
    LitE{}     -> return ex
    FloatE{}   -> return ex
    LitSymE{}  -> return ex
    AppE{}     -> return ex
    PrimAppE{} -> return ex
    DataConE{} -> return ex
    ProjE i e  -> ProjE i <$> go e
    IfE a b c  -> (IfE a) <$> go b <*> go c
    MkProdE ls -> MkProdE <$> mapM go ls
    LetE (v,locs,ty,rhs) bod -> LetE <$> (v,locs,ty,) <$> go rhs <*> go bod
    CaseE scrt mp -> (CaseE scrt) <$> mapM (\(a,b,c) -> (a,b,) <$> go c) mp
    TimeIt e ty b -> do
      e' <- go e
      return $ TimeIt e' ty b
    SpawnE{} -> pure ex
    SyncE{}  -> pure ex
    WithArenaE v e -> WithArenaE v <$> go e
    MapE{}  -> error $ "inferRegScopeExp: TODO MapE"
    FoldE{} -> error $ "inferRegScopeExp: TODO FoldE"
  where
    go = tagRANExp
