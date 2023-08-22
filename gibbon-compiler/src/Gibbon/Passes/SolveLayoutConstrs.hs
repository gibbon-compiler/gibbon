module Gibbon.Passes.SolveLayoutConstrs
  ( solveConstrs
  ) where

import           Gibbon.Common
import           Gibbon.L1.Syntax

import           Gibbon.Language.Syntax

import           Control.Monad.State              (lift)
import           Data.Int
import qualified Data.List                        as L
import           Data.Maybe                       (fromJust)
import qualified Data.Set                         as S
import           GHC.Float
import           Prelude                          as P
import           System.Exit
import           System.IO
import           System.Process
import           System.Random

import qualified Language.Python.Common.AST       as Py
import qualified Language.Python.Common.Pretty    as Py
import qualified Language.Python.Common.PrettyAST as Py


--------------------------------------------------------------------------------

-- new positions of fields
type Layout = [(Int, Int)]


-- change if required
python3 :: String
python3 = "python3"

solveConstrs :: [Constr] -> IO Layout
solveConstrs constrs = do
  let pycode = fst $ defaultRunPassM (pythonCodegen constrs)
  uniq <- randomIO :: IO Int8
  let fp = "./solve_ilp_" ++ show uniq ++ ".py"
  writeFile fp pycode
  let cmd = python3 ++ " " ++ fp
  (_, Just hout, Just herr, phandle) <-
    createProcess (shell cmd) {std_out = CreatePipe, std_err = CreatePipe}
  exitCode <- waitForProcess phandle
  case exitCode of
    ExitSuccess -> do
      out <- hGetContents hout
      let new_positions :: [(Int, Int)] =
            map ((\(x, y) -> (float2Int x, float2Int y)) . read) (lines out)
      pure new_positions
    ExitFailure n ->
      error $
      "Running docplex program in file " ++
      fp ++ " exited with error code  " ++ show n

pythonCodegen :: [Constr] -> PassM String
pythonCodegen constrs
  -- There should be a map mapping indexes to the generated variables
  -- 3 maps for different constraints
  -- Here have a map to seperate the soft constraints and pass as usual
 = do
  let idxs =
        L.nub $
        P.concatMap
          (\a ->
             case a of
               Soft ((a, b), _) -> [a, b]
               _                -> [])
          constrs
  let softConstr =
        P.concatMap
          (\a ->
             case a of
               Soft a -> [a]
               _      -> [])
          constrs
  let immediateConstrVariables =
        L.nub $
        P.concatMap
          (\a ->
             case a of
               Imm (a, b) -> [a, b]
               _          -> [])
          constrs
  
-- filter out the relative constraints.
  -- don't need integers in snd part of tuple since they are positions that need to be assigned not for creating variables.
  let relativeConstrs =
        P.concatMap
          (\a ->
             case a of
               Imm a -> [a]
               _     -> [])
          constrs
  let absConstrVariables =
        L.nub $
        P.concatMap
          (\a ->
             case a of
               Absolute (a, b) -> [a]
               _               -> [])
          constrs
  let strongConstraints =
        P.concatMap
          (\a ->
             case a of
               Absolute a -> [a]
               _          -> [])
          constrs
  
-- [ (field_index, variable_name)  ]
  node_map <-
    mapM
      (\i -> (i, ) <$> fromVar <$> gensym (toVar ("x_" ++ show i)))
      (L.nub $ (idxs ++ immediateConstrVariables ++ absConstrVariables))
  let node_vars = P.concatMap (\(i, var) -> [var]) node_map
  model_var <- (\i -> "model_" ++ show i) <$> newUniq
  let init_model =
        Py.Assign
          [Py.Var (pyident model_var) ()]
          (Py.Call (Py.Var (pyident "Model") ()) [] ())
          ()
  
-- make a map for upper, lower bounds.
  let (lb, ub) =
        ( fromIntegral $ 0
        , fromIntegral $
          (P.length (L.nub $ (idxs ++ immediateConstrVariables))) - 1)
  let soft_rel_to_ub =
        P.map
          (\index -> (fromJust $ lookup index node_map, ub))
          (idxs ++ immediateConstrVariables)
  let abs_ub =
        P.map (\(x, y) -> (fromJust $ lookup x node_map, y)) strongConstraints
  let vars_ub = soft_rel_to_ub ++ abs_ub
  let init_nodes =
        map
          (\x ->
             pyassign1
               x
               (Py.Call
                  (Py.Dot (pyvar model_var) (pyident "integer_var") ())
                  [ Py.ArgKeyword (pyident "lb") (Py.Int lb (show lb) ()) ()
                  , Py.ArgKeyword
                      (pyident "ub")
                      (Py.Int
                         (fromJust $ lookup x vars_ub)
                         (show (fromJust $ lookup x vars_ub))
                         ())
                      ()
                  , Py.ArgKeyword (pyident "name") (Py.Strings [show x] ()) ()
                  ]
                  ()))
          node_vars
  let num_edges =
        P.sum $
        P.map
          (\a ->
             case a of
               Soft _ -> 1
               _      -> 0)
          constrs
  cost_map <-
    mapM (\i -> (i, ) <$> fromVar <$> gensym (toVar "cost")) [1 .. num_edges]
  let cost_vars = map snd cost_map
  let import_doplex =
        Py.FromImport
          (Py.ImportRelative
             0
             (Just [pyident "docplex", pyident "mp", pyident "model"])
             ())
          (Py.FromItems [Py.FromItem (pyident "Model") Nothing ()] ())
          ()
  let init_costs =
        map
          (\x ->
             pyassign1
               x
               (Py.Call
                  (Py.Dot (pyvar model_var) (pyident "integer_var") ())
                  [Py.ArgKeyword (pyident "name") (Py.Strings [show x] ()) ()]
                  ()))
          cost_vars
  minimize_parts <-
    mapM (\_ -> fromVar <$> gensym (toVar "min")) [1 .. num_edges]
  let constrs_for_edge =
        (\(((from, to), wt), cost, minimize_part) -> do
           let x = fromJust $ lookup from node_map
           let y = fromJust $ lookup to node_map
                            -- let cost_x = fromJust $ lookup from cost_map -- Vidush review
           eq_minus_one <- fromVar <$> (gensym "cost")
           leq_minus_one <- fromVar <$> (gensym "cost")
           eq_one <- fromVar <$> (gensym "cost")
           geq_one <- fromVar <$> (gensym "cost")
           neq_minus_one <- fromVar <$> (gensym "cost")
           neq_one <- fromVar <$> (gensym "cost")
           x_minus_y <- fromVar <$> (gensym "x_minus_y")
           pure $
             [ pyassign1
                 x_minus_y
                 (Py.Paren (Py.BinaryOp (Py.Minus ()) (pyvar x) (pyvar y) ()) ())
             , pyassign1
                 eq_minus_one
                 (Py.Paren
                    (Py.BinaryOp
                       (Py.Equality ())
                       (pyvar x_minus_y)
                       (Py.Int (-1) (show (-1)) ())
                       ())
                    ())
             , pyassign1
                 leq_minus_one
                 (Py.Paren
                    (Py.BinaryOp
                       (Py.LessThanEquals ())
                       (pyvar x_minus_y)
                       (Py.Int (-1) (show (-1)) ())
                       ())
                    ())
             , pyassign1
                 eq_one
                 (Py.Paren
                    (Py.BinaryOp
                       (Py.Equality ())
                       (pyvar x_minus_y)
                       (Py.Int 1 (show 1) ())
                       ())
                    ())
             , pyassign1
                 geq_one
                 (Py.Paren
                    (Py.BinaryOp
                       (Py.GreaterThanEquals ())
                       (pyvar x_minus_y)
                       (Py.Int 1 (show 1) ())
                       ())
                    ())
             , pyassign1
                 neq_minus_one
                 (Py.Paren
                    (Py.BinaryOp
                       (Py.NotEquals ())
                       (pyvar x_minus_y)
                       (Py.Int (-1) (show (-1)) ())
                       ())
                    ())
             , pyassign1
                 neq_one
                 (Py.Paren
                    (Py.BinaryOp
                       (Py.NotEquals ())
                       (pyvar x_minus_y)
                       (Py.Int 1 (show 1) ())
                       ())
                    ())
             , Py.StmtExpr
                 (Py.Call
                    (Py.Dot (pyvar model_var) (pyident "add") ())
                    [ Py.ArgExpr
                        (Py.BinaryOp
                           (Py.LessThanEquals ())
                           (pyvar eq_minus_one)
                           (Py.Paren
                              (Py.BinaryOp
                                 (Py.Equality ())
                                 (pyvar cost)
                                 (Py.Int 0 (show 0) ())
                                 ())
                              ())
                           ())
                        ()
                    ]
                    ())
                 ()
             , Py.StmtExpr
                 (Py.Call
                    (Py.Dot (pyvar model_var) (pyident "add") ())
                    [ Py.ArgExpr
                        (Py.BinaryOp
                           (Py.LessThanEquals ())
                           (Py.Paren
                              (Py.BinaryOp
                                 (Py.BinaryAnd ())
                                 (pyvar leq_minus_one)
                                 (pyvar neq_minus_one)
                                 ())
                              ())
                           (Py.Paren
                              (Py.BinaryOp
                                 (Py.Equality ())
                                 (pyvar cost)
                                 (Py.Int 100 (show 100) ())
                                 ())
                              ())
                           ())
                        ()
                    ]
                    ())
                 ()
             , Py.StmtExpr
                 (Py.Call
                    (Py.Dot (pyvar model_var) (pyident "add") ())
                    [ Py.ArgExpr
                        (Py.BinaryOp
                           (Py.LessThanEquals ())
                           (pyvar eq_one)
                           (Py.Paren
                              (Py.BinaryOp
                                 (Py.Equality ())
                                 (pyvar cost)
                                 (Py.Int 200 (show 200) ())
                                 ())
                              ())
                           ())
                        ()
                    ]
                    ())
                 ()
             , Py.StmtExpr
                 (Py.Call
                    (Py.Dot (pyvar model_var) (pyident "add") ())
                    [ Py.ArgExpr
                        (Py.BinaryOp
                           (Py.LessThanEquals ())
                           (Py.Paren
                              (Py.BinaryOp
                                 (Py.BinaryAnd ())
                                 (pyvar geq_one)
                                 (pyvar neq_one)
                                 ())
                              ())
                           (Py.Paren
                              (Py.BinaryOp
                                 (Py.Equality ())
                                 (pyvar cost)
                                 (Py.Int 300 (show 300) ())
                                 ())
                              ())
                           ())
                        ()
                    ]
                    ())
                 ()
             , pyassign1
                 minimize_part
                 (Py.BinaryOp
                    (Py.Multiply ())
                    (pyvar cost)
                    (Py.Int wt (show wt) ())
                    ())
             ]) :: ((((Integer, Integer), Integer), String, String) -> PassM [(Py.Statement ())])
  constrs_for_edges <-
    concat <$> mapM constrs_for_edge (zip3 softConstr cost_vars minimize_parts)
  let expr_to_minimize =
        foldr
          (\x acc -> Py.BinaryOp (Py.Plus ()) (pyvar x) acc ())
          (Py.Int 0 (show 0) ())
          minimize_parts
  let call_minimize =
        Py.StmtExpr
          (Py.Call
             (Py.Dot (pyvar model_var) (pyident "minimize") ())
             [(Py.ArgExpr expr_to_minimize ())]
             ())
          ()
  -- All the fields should have unique index positions.
  let uniq_constrs =
        map
          (\[i, j] ->
             Py.StmtExpr
               (Py.Call
                  (Py.Dot (pyvar model_var) (pyident "add") ())
                  [ Py.ArgExpr
                      (Py.BinaryOp (Py.NotEquals ()) (pyvar i) (pyvar j) ())
                      ()
                  ]
                  ())
               ())
          (combinations 2 node_vars)
  soln_var <- fromVar <$> (gensym "soln")
  let call_solve =
        pyassign1
          soln_var
          (Py.Call (Py.Dot (pyvar model_var) (pyident "solve") ()) [] ())
  let answer_format_str = "({},{})"
  let print_left_bracket =
        Py.StmtExpr
          (Py.Call
             (pyvar "print")
             [Py.ArgExpr (Py.Strings [(show "[")] ()) ()]
             ())
          ()
  let print_right_bracket =
        Py.StmtExpr
          (Py.Call
             (pyvar "print")
             [Py.ArgExpr (Py.Strings [(show "]")] ()) ()]
             ())
          ()
  let print_answers =
        map
          (\(i, v) ->
             Py.StmtExpr
               (Py.Call
                  (pyvar "print")
                  [ (Py.ArgExpr
                       (Py.Call
                          (Py.Dot
                             (Py.Strings [show answer_format_str] ())
                             (pyident "format")
                             ())
                          [ Py.ArgExpr (Py.Int i (show i) ()) ()
                          , Py.ArgExpr
                              (Py.Call
                                 (Py.Dot
                                    (pyvar soln_var)
                                    (pyident "get_value")
                                    ())
                                 [Py.ArgExpr (pyvar v) ()]
                                 ())
                              ()
                          ]
                          ())
                       ())
                  ]
                  ())
               ())
          node_map
   
-- make the relative constraints is they exist
  let relativeConstrsBindings =
        P.map
          (\(x, y) ->
             Py.StmtExpr
               (Py.Call
                  (Py.Dot (pyvar model_var) (pyident "add") ())
                  [ Py.ArgExpr
                      (Py.BinaryOp
                         (Py.Equality ())
                         (pyvar (fromJust $ lookup y node_map))
                         (Py.BinaryOp
                            (Py.Plus ())
                            (pyvar (fromJust $ lookup x node_map))
                            ((Py.Int 1 (show 1) ()))
                            ())
                         ())
                      ()
                  ]
                  ())
               ())
          relativeConstrs
  let absolute_ordering_constrs =
        P.map
          (\(x, y) ->
             Py.StmtExpr
               (Py.Call
                  (Py.Dot (pyvar model_var) (pyident "add") ())
                  [ Py.ArgExpr
                      (Py.BinaryOp
                         (Py.Equality ())
                         (pyvar (fromJust $ lookup x node_map))
                         ((Py.Int y (show y) ()))
                         ())
                      ()
                  ]
                  ())
               ())
          strongConstraints
  let stmts =
        [import_doplex, init_model] ++
        init_nodes ++
        init_costs ++
        constrs_for_edges ++
        uniq_constrs ++
        relativeConstrsBindings ++
        absolute_ordering_constrs ++
        [call_minimize, call_solve] ++ print_answers
  let pycode = Py.prettyText (Py.Module stmts)
  pure pycode --dbgTraceIt (sdoc node_vars) (dbgTraceIt "\n")


-- https://stackoverflow.com/a/52605612
combinations :: Int -> [a] -> [[a]]
combinations k ns = filter ((k ==) . length) $ L.subsequences ns


--------------------------------------------------------------------------------
pyident :: String -> Py.Ident ()
pyident s = Py.Ident s ()

pyvar :: String -> Py.Expr ()
pyvar s = Py.Var (pyident s) ()

pyassign1 :: String -> Py.Expr () -> Py.Statement ()
pyassign1 v rhs = Py.Assign [pyvar v] rhs ()
