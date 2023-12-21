module Gibbon.Passes.ElimNewtype where

import Gibbon.L1.Syntax
import Gibbon.Common

import Control.Arrow
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Symbol (unintern)

passProgram :: Prog1 -> Prog1
passProgram prog = 
  Prog 
    { mainExp= (elimE connames *** elimTy tynames) <$> mainExp prog
    , fundefs= fdefs
    , ddefs=tys
    }
  where
    (newtys, tys) = M.partition (\x -> case dataCons x of
        [(_, [_])] -> True
        _ -> False
      ) (ddefs prog)
    tynames = S.fromList $ (\(Var x) -> unintern x) <$> M.keys newtys
    connames = S.fromList $ fst . head . dataCons <$> M.elems newtys
    fdefs = M.map (\d -> d {funTy=elimTyArrow tynames (funTy d)}) (fundefs prog)

elimE :: S.Set String -> Exp1 -> Exp1
elimE cns e0 = case e0 of
  DataConE _ty0 s es -> _
  _ -> _

elimTyArrow :: S.Set String -> ([Ty1], Ty1) -> ([Ty1], Ty1)
elimTyArrow tns = fmap (elimTy tns) *** elimTy tns

elimTy :: S.Set String -> Ty1 -> Ty1
elimTy tns _ = _
