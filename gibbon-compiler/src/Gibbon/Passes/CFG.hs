{-# LANGUAGE FlexibleContexts #-}

module Gibbon.Passes.CFG where

import Data.Graph
import Data.Maybe ( fromJust )
import qualified Data.Map as M
import qualified Data.Set as S
import Gibbon.L1.Syntax
import Gibbon.Common

--------------------------------------------------------------------------------

type Label = String
type Node = Var

expr1 :: Exp1
expr1 = LetE ("x", [], IntTy, LitE 1) $
        LetE ("y", [], IntTy, PrimAppE AddP [VarE "x", LitE 1]) $
        VarE "x"

cfg :: IO ()
cfg = do
  let ((labels_map, edge_map), _) = defaultRunPassM $ go M.empty [] expr1
  let (g, nodeFromVertex, vertexFromKey) = graphFromEdges edge_map
  let lbl_x = labels_map # "x"
  let lbl_y = labels_map # "y"
  let vx = (fromJust $ vertexFromKey lbl_x)
  let vy = (fromJust $ vertexFromKey lbl_y)
  print (path g vy vx)
 where
  go labels_map edge_map expr =
    case expr of
      VarE{} -> pure (labels_map, edge_map)
      LetE (v,locs,ty,rhs) bod -> do
        lbl <- fromVar <$> gensym "lbl"
        let deps = map (\dep -> (v, lbl, [dep])) $
                   map (labels_map #) $
                   S.toList (gFreeVars rhs)
        let deps' = if null deps then [(v, lbl, [])] else deps
        let labels_map' = M.insert v lbl labels_map
        go labels_map' (deps' ++ edge_map) bod
