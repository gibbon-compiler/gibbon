module Gibbon.Passes.ElimNewtype where

import Gibbon.L1.Syntax
import Gibbon.Common

import qualified Data.Map as M

passProgram :: Prog1 -> Prog1
passProgram prog = 
  _
  where
    _ = ddefs prog  -- filter out cases of size 1
  
  
  -- hcat
  -- [ ppDDefs $ ddefs prog
  -- , ppFunDefs $ fundefs prog
  -- , ppMainExpr $ mainExp prog
  -- , "\n"
  -- ]

-- elimE :: Exp1 -> Exp1
-- elimE e0 = case e0 of
--   DataConE _ty0 s es -> _
--   _ -> _
