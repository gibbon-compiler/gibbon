module Gibbon.NewL2.FromOldL2 ( fromOldL2 ) where

import qualified Data.Map as M
import qualified Data.Set as S

import qualified Gibbon.L2.Syntax as Old
import           Gibbon.NewL2.Syntax as New
import           Gibbon.Common

--------------------------------------------------------------------------------

-- Maps a location to a region
type LocEnv = M.Map LocVar LocArg

fromOldL2 :: Old.Prog2 -> PassM New.Prog2
fromOldL2 Prog{ddefs,fundefs,mainExp} = do
  fds' <- mapM (fromOldL2Fn ddefs fundefs) $ M.elems fundefs
  let fundefs' = M.fromList $ map (\f -> (funName f,f)) fds'
      env2 = Env2 M.empty (initFunEnv fundefs)
  mainExp' <- case mainExp of
                Nothing -> return Nothing
                Just (mn, ty) -> Just . (,ty) <$>
                  fromOldL2Exp ddefs fundefs M.empty env2 mn
  -- return $ Prog ddefs fundefs' mainExp'
  _todo


fromOldL2Fn :: DDefs Old.Ty2 -> Old.FunDefs2 -> Old.FunDef2 -> PassM New.FunDef2
fromOldL2Fn ddefs fundefs f@FunDef{funName,funArgs,funTy,funBody} = do
  let initTyEnv  = M.fromList $ zip funArgs (Old.arrIns funTy)
      env2 = Env2 initTyEnv (initFunEnv fundefs)
      initLocEnv = M.fromList $ map (\lrm -> (Old.lrmLoc lrm, Loc lrm)) (Old.locVars funTy)
  bod' <- fromOldL2Exp ddefs fundefs initLocEnv env2 funBody
  _todo
  -- return $ f {funBody = bod''}


fromOldL2Exp :: DDefs Old.Ty2 -> Old.FunDefs2 -> LocEnv -> Env2 Old.Ty2 -> Old.Exp2 -> PassM New.Exp2
fromOldL2Exp ddefs fundefs locenv env2 ex = _todo
