module Gibbon.Passes.ControlFlowGraph
  ( getFunctionCFG
  , CFGfunctionMap(..)
  ) where


-- Gibbon Imports
import           Gibbon.Common
import           Gibbon.Language
import           Gibbon.Language.Syntax

import           Control.Monad          as Monad
import           Data.Graph             as G
import           Data.List              as L
import           Data.Map               as M
import           Data.Maybe             as Maybe
import           Data.Set               as S

-- Haskell Imports
import           Prelude                as P
import           Text.PrettyPrint.GenericPretty

-- | CFGfunctionMap ex, a map storing a function, represented by Var (function name) to its control flow graph
-- | Edge == (ex, Integer) the IR expression and its corresponding probability
-- | See Data.Containers for detailed definition about how the graph is stored and represented.
type CFGfunctionMap ex
   = M.Map Var ( G.Graph
               , G.Vertex -> ((ex, Integer), Integer, [Integer])
               , Integer -> Maybe G.Vertex)


-- -- | Takes a map, list of function definitions, return update map with CFG for each funciton in the list
-- generateCfgFunctions :: CFGfunctionMap -> FieldMap -> [FunDef (PreExp e l d)] -> DataCon -> (CFGfunctionMap, FieldMap)
-- generateCfgFunctions cfgMap fieldMap defs datacon =
--     case defs of
--         [] -> (cfgMap, fieldMap)
--         x:xs -> let
--                     (cfgMapNew, edgeList, fieldGraphEdges) = generateCfgFunction cfgMap x datacon
--                     dconAccessMap   = M.insert datacon fieldGraphEdges (M.empty)
--                     updatedFieldMap = M.insert x dconAccessMap fieldMap
--                   in generateCfgFunctions cfgMapNew updatedFieldMap xs datacon

-- -- |  Generate a CFG for the corresponsing function
-- generateCfgFunction :: CFGfunctionMap -> FunDef (PreExp e l d) -> DataCon -> (CFGfunctionMap, [(((PreExp e l d), Integer) , Integer, [Integer])], [((Integer, Integer), Integer)])
-- generateCfgFunction cfgMap f@FunDef { funName, funBody, funTy, funArgs } datacon =
--     let (edgeList, succ, maxDepth) = generateCFGExp 0 100 funBody
--         (graph, nodeFromVertex, vertexFromKey) = G.graphFromEdges edgeList
--         newCFGMap = M.insert f (graph, nodeFromVertex, vertexFromKey) cfgMap
--         topSortedVertices  = topSort graph
--         topSortedNodes = P.map nodeFromVertex topSortedVertices
--         map = backtrackVariablesToDataConFields topSortedNodes
--         edges = constructFieldGraph Nothing nodeFromVertex vertexFromKey topSortedNodes topSortedNodes map datacon
--      in (newCFGMap, edgeList, edges)
--     -- dbgTraceIt (sdoc varList) dbgTraceIt ("\n") dbgTraceIt (sdoc varList') dbgTraceIt ("\n")
--     -- dbgTraceIt (sdoc x') dbgTraceIt ("\n") dbgTraceIt (sdoc map) dbgTraceIt ("\n")
--     -- pure (cfgMap, edgeList)
--     -- dbgTraceIt (sdoc x) dbgTraceIt (sdoc x') dbgTraceIt ("\n") dbgTraceIt (sdoc edges) dbgTraceIt ("\n") pure (cfgMap, edgeList)

-- | Generate a CFG out of a Function definition.
-- | Returns a map mapping a function to its corresponding CFG
getFunctionCFG :: (Out l, Out d, Out (e l d)) => FunDef (PreExp e l d) -> CFGfunctionMap (PreExp e l d)
getFunctionCFG f@FunDef {funName, funBody, funTy, funArgs} =
  let (edgeList, _, _) = generateCFGExp 0 100 funBody
      (graph, nodeFromVertex, vertexFromKey) = G.graphFromEdges edgeList
   in  M.insert funName (graph, nodeFromVertex, vertexFromKey) (M.empty) --dbgTraceIt (sdoc edgeList)


-- | generate the Edges from the IR expression.
generateCFGExp ::
     Integer
  -> Integer
  -> (PreExp e l d)
  -> ([(((PreExp e l d), Integer), Integer, [Integer])], Integer, Integer)
generateCFGExp vertexCounter edgeWeight exp =
  case exp of
    DataConE loc dcon args ->
      let edge = ((exp, edgeWeight), vertexCounter, [])
       in ([edge], vertexCounter, vertexCounter)
    VarE {} ->
      let edge = ((exp, edgeWeight), vertexCounter, [])
       in ([edge], vertexCounter, vertexCounter)
    LitE {} ->
      let edge = ((exp, edgeWeight), vertexCounter, [])
       in ([edge], vertexCounter, vertexCounter)
    CharE {} ->
      let edge = ((exp, edgeWeight), vertexCounter, [])
       in ([edge], vertexCounter, vertexCounter)
    FloatE {} ->
      let edge = ((exp, edgeWeight), vertexCounter, [])
       in ([edge], vertexCounter, vertexCounter)
    LitSymE {} ->
      let edge = ((exp, edgeWeight), vertexCounter, [])
       in ([edge], vertexCounter, vertexCounter)
    AppE f locs args ->
      let (edgeList, succList, maxDepth) =
            processExpListSeq (vertexCounter + 1) edgeWeight args
          edge = (((VarE f), edgeWeight), vertexCounter, succList)
          newEdges = edgeList ++ [edge]
       in (newEdges, vertexCounter, maxDepth)
    PrimAppE f args ->
      let (edgeList, succList, maxDepth) =
            processExpListSeq (vertexCounter + 1) edgeWeight args
          edge = ((exp, edgeWeight), vertexCounter, succList)
          newEdges = edgeList ++ [edge]
       in (newEdges, vertexCounter, maxDepth)
    LetE (v, loc, ty, rhs) bod ->
      let (edgeList, succ, maxDepth) =
            generateCFGExp (vertexCounter + 1) edgeWeight bod
          exp' = LetE (v, loc, ty, rhs) $ VarE v
          edge = ((exp', edgeWeight), vertexCounter, [succ])
          edgeList' = edgeList ++ [edge]
       in (edgeList', vertexCounter, maxDepth)
    CaseE scrt mp ->
      let (edgeList, succList, maxDepth) =
            processExpSeqCase
              (vertexCounter + 1)
              (edgeWeight `div` (P.toInteger (P.length mp)))
              mp
          edge = ((scrt, edgeWeight), vertexCounter, succList)
          newEdges = edgeList ++ [edge]
       in (newEdges, vertexCounter, maxDepth)
    IfE a b c ->
      let (edgeListB, succB, d1) =
            generateCFGExp (vertexCounter + 1) (edgeWeight `div` 2) b
          (edgeListC, succC, d2) =
            generateCFGExp (d1 + 1) (edgeWeight `div` 2) c
          succList = [succB, succC]
          edge = ((a, edgeWeight), vertexCounter, succList)
          newEdges = edgeListB ++ edgeListC ++ [edge]
       in (newEdges, vertexCounter, P.maximum [d1, d2])
    MkProdE xs ->
      let (edgeList, succList, maxDepth) =
            processExpListSeq (vertexCounter + 1) edgeWeight xs
          edge = ((exp, edgeWeight), vertexCounter, succList)
          newEdges = edgeList ++ [edge]
       in (newEdges, vertexCounter, maxDepth)
    ProjE i e -> error "generateCFGExp: TODO ProjE"
    TimeIt e ty b -> error "generateCFGExp: TODO TimeIt"
    WithArenaE v e -> error "generateCFGExp: TODO WithArenaE"
    SpawnE f locs args -> error "generateCFGExp: TODO SpawnE"
    SyncE -> error "generateCFGExp: TODO SyncE"
    Ext _ -> error "generateCFGExp: TODO Ext"
    MapE {} -> error "generateCFGExp: TODO MapE"
    FoldE {} -> error "generateCFGExp: TODO FoldE"


-- | Process a list of expressions seqientially rather than in parallel
-- | Otherwise threading an integer becomes difficult
processExpListSeq ::
     Integer
  -> Integer
  -> [(PreExp e l d)]
  -> ([(((PreExp e l d), Integer), Integer, [Integer])], [Integer], Integer)
processExpListSeq currVertex edgeWeight exp =
  case exp of
    [] -> ([], [], currVertex)
    x:xs ->
      let (edgeList, succ, maxDepth) = generateCFGExp currVertex edgeWeight x
          (edgeList', succ', maxDepth') =
            processExpListSeq (maxDepth + 1) edgeWeight xs
          newEdgeList = edgeList ++ edgeList'
          succList = [succ] ++ succ'
       in (newEdgeList, succList, maxDepth')


-- | Process a list of case expressions sequentially rather than in parallel
processExpSeqCase ::
     Integer
  -> Integer
  -> [(DataCon, [(Var, loc)], (PreExp e l d))]
  -> ([(((PreExp e l d), Integer), Integer, [Integer])], [Integer], Integer)
processExpSeqCase currVertex edgeWeight lst =
  case lst of
    [] -> ([], [], currVertex)
    x:xs ->
      let (edgeList, succ, maxDepth) =
            generateVerticesCase currVertex edgeWeight x
          (edgeList', succList, maxDepth') =
            processExpSeqCase (maxDepth + 1) edgeWeight xs
          newEdgeList = edgeList ++ edgeList'
          succList' = [succ] ++ succList
       in (newEdgeList, succList', maxDepth')


-- | Helper function to generate a vertex for each case binding
generateVerticesCase ::
     Integer
  -> Integer
  -> (DataCon, [(Var, loc)], (PreExp e l d))
  -> ([(((PreExp e l d), Integer), Integer, [Integer])], Integer, Integer)
generateVerticesCase currVertex edgeWeight branch =
  let datacon = fst3 branch
      fields_locs = snd3 branch
      fields = P.map (\x -> (VarE (fst x))) fields_locs
      dataconExp = DataConE _ datacon fields
      (edgeList, succ, maxDepth) =
        generateCFGExp (currVertex + 1) edgeWeight (thd3 branch)
      edge = ((dataconExp, edgeWeight), currVertex, [succ])
      newEdges = edgeList ++ [edge]
   in (newEdges, currVertex, maxDepth)
