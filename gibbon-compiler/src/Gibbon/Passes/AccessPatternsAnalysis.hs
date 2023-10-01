module Gibbon.Passes.AccessPatternsAnalysis
  ( generateAccessGraphs,
    getGreedyOrder,
    FieldMap,
    DataConAccessMap,
  )
where

-- Gibbon imports

import Control.Monad as Mo
import Data.Graph as G
import Data.List as L
import Data.Map as M
import Data.Maybe as Mb
import Data.Set as S
import Gibbon.Common
import Gibbon.Language
import Gibbon.Language.Syntax
import Gibbon.Passes.ControlFlowGraph (CFGfunctionMap)
-- Haskell imports

import Text.PrettyPrint.GenericPretty
import Prelude as P

-- | Type VariableMap: Stores mapping from Variable to wheather it comes from a particular datacon
-- | index position in data con.
type VariableMap = M.Map Var (Maybe (DataCon, Integer))

-- | Map a function to its Access map for a particular data constructor.
-- | Function stored as variable name
type FieldMap = M.Map Var DataConAccessMap

-- | Store the access edges for fields in a data con.
-- | Fields are represented as index positions in the DataCon.
type DataConAccessMap = M.Map DataCon [((Integer, Integer), Integer)]

generateAccessGraphs ::
  (FreeVars (e l d), Ord l, Ord d, Ord (e l d), Out d, Out l) =>
  CFGfunctionMap (PreExp e l d) ->
  FieldMap ->
  FunDef (PreExp e l d) ->
  DataCon ->
  FieldMap
generateAccessGraphs
  cfgMap
  fieldMap
  funDef@FunDef
    { funName,
      funBody,
      funTy,
      funArgs
    }
  dcons =
    case (M.lookup funName cfgMap) of
      Just (graph, nodeFromVertex, vertexFromKey) ->
        let topologicallySortedVertices = topSort graph
            topologicallySortedNodes =
              P.map nodeFromVertex topologicallySortedVertices
            map = backtrackVariablesToDataConFields topologicallySortedNodes dcons
            edges = S.toList $ S.fromList $
                ( constructFieldGraph
                    Nothing
                    nodeFromVertex
                    vertexFromKey
                    topologicallySortedNodes
                    topologicallySortedNodes
                    map
                )
                dcons
            accessMapsList = zipWith (\x y -> (x, y)) [dcons] [edges]
            accessMaps = M.fromList accessMapsList
         in M.insert funName accessMaps fieldMap  --dbgTraceIt (sdoc topologicallySortedVertices) dbgTraceIt ("\n") dbgTraceIt (sdoc (topologicallySortedVertices, edges)) dbgTraceIt ("\n") 
      Nothing -> error "generateAccessGraphs: no CFG for function found!"



getGreedyOrder :: [((Integer, Integer), Integer)] -> Int -> [Integer]
getGreedyOrder edges fieldLength = 
          if edges == []
            then P.map P.toInteger [0 .. (fieldLength - 1)] 
            else 
              let partial_order = greedyOrderOfVertices edges
                  completeOrder = P.foldl (\lst val -> if S.member val (S.fromList lst) then lst
                                                 else lst ++ [val]
                                    ) partial_order [0 .. (fieldLength - 1)]
                in dbgTraceIt (sdoc (edges, completeOrder)) P.map P.toInteger completeOrder

greedyOrderOfVertices :: [((Integer, Integer), Integer)] -> [Int]
greedyOrderOfVertices ee = let     edges' = P.map (\((a, b), c) -> ((P.fromIntegral a, P.fromIntegral b), P.fromIntegral c)) ee
                                   bounds = (\e -> let v = P.foldr (\((i, j), _) s -> S.insert j (S.insert i s)) S.empty e
                                                       mini  = minimum v
                                                       maxi  = maximum v
                                                    in (mini, maxi)
                                            ) edges'
                                   edgesWithoutWeight = P.map fst edges'
                                   graph = buildG bounds edgesWithoutWeight
                                   weightMap = P.foldr (\(e, w) mm -> M.insert e w mm) M.empty edges'
                                   v'' = greedyOrderOfVerticesHelper graph (topSort graph) weightMap S.empty
                                in v'' -- dbgTraceIt (sdoc (v'', (M.elems weightMap)))


greedyOrderOfVerticesHelper :: Graph -> [Int] -> M.Map (Int, Int) Int -> S.Set Int -> [Int]
greedyOrderOfVerticesHelper graph vertices' weightMap visited = case vertices' of
  [] -> []
  x:xs -> if S.member x visited
          then greedyOrderOfVerticesHelper graph xs weightMap visited
          else let successors = reachable graph x
                   removeCurr = S.toList $ S.delete x (S.fromList successors)
                   orderedSucc = orderedSuccsByWeight removeCurr x weightMap visited
                   visited' = P.foldr S.insert S.empty orderedSucc
                   v'' = greedyOrderOfVerticesHelper graph xs weightMap visited'
                in if successors == [x] 
                   then orderedSucc ++ v'' --dbgTraceIt (sdoc (v'', orderedSucc))
                   else [x] ++ orderedSucc ++ v''

orderedSuccsByWeight :: [Int] -> Int -> M.Map (Int, Int) Int -> S.Set Int -> [Int]
orderedSuccsByWeight s i weightMap visited = case s of
                                        [] -> []
                                        _  -> let vertexWithMaxWeight = P.foldr (\v (v', maxx) -> let w = M.lookup (i, v) weightMap
                                                                                                        in case w of
                                                                                                               Nothing -> (-1, -1)
                                                                                                               Just w' -> if w' > maxx
                                                                                                                          then (v, w')
                                                                                                                          else (v', maxx)
                                                                     ) (-1, -1) s
                                                in if fst vertexWithMaxWeight == -1
                                                   then []
                                                   else
                                                    let removeVertexWithMaxWeight = S.toList $ S.delete (fst vertexWithMaxWeight) (S.fromList s)
                                                     in if S.member (fst vertexWithMaxWeight) visited
                                                        then orderedSuccsByWeight removeVertexWithMaxWeight i weightMap visited 
                                                        else fst vertexWithMaxWeight : orderedSuccsByWeight removeVertexWithMaxWeight i weightMap visited --dbgTraceIt (sdoc (s, removeVertexWithMaxWeight, vertexWithMaxWeight))




backtrackVariablesToDataConFields ::
  (FreeVars (e l d), Ord l, Ord d, Ord (e l d), Out d, Out l) =>
  [(((PreExp e l d), Integer), Integer, [Integer])] ->
  DataCon ->
  VariableMap
backtrackVariablesToDataConFields graph dcon =
  case graph of
    [] -> M.empty
    x : xs ->
      let newMap = processVertex graph x M.empty dcon
          mlist = M.toList (newMap)
          m = backtrackVariablesToDataConFields xs dcon
          mlist' = M.toList m
          newMap' = M.fromList (mlist ++ mlist')
       in newMap'

processVertex ::
  (FreeVars (e l d), Ord l, Ord d, Ord (e l d), Out d, Out l) =>
  [(((PreExp e l d), Integer), Integer, [Integer])] ->
  (((PreExp e l d), Integer), Integer, [Integer]) ->
  VariableMap ->
  DataCon ->
  VariableMap
processVertex graph node map dataCon  =
  case node of
    ((expression, likelihood), id, succ) ->
      case expression of
        DataConE loc dcon args ->
          if dcon == dataCon
          then
            let freeVariables = L.concat (P.map (\x -> S.toList (gFreeVars x)) args)
                maybeIndexes = P.map (getDataConIndexFromVariable graph) freeVariables
                mapList = M.toList map
                newMapList = P.zipWith (\x y -> (x, y)) freeVariables maybeIndexes
             in M.fromList (mapList ++ newMapList)
          else map
        _ -> map

getDataConIndexFromVariable ::
  (FreeVars (e l d), Ord l, Ord d, Ord (e l d), Out d, Out l) =>
  [(((PreExp e l d), Integer), Integer, [Integer])] ->
  Var ->
  Maybe (DataCon, Integer)
getDataConIndexFromVariable graph variable =
  case graph of
    [] -> Nothing
    x : xs ->
      let status = compareVariableWithDataConFields x variable
       in case status of
            Nothing -> getDataConIndexFromVariable xs variable
            Just val -> Just val

compareVariableWithDataConFields ::
  (FreeVars (e l d), Ord l, Ord d, Ord (e l d), Out d, Out l) =>
  (((PreExp e l d), Integer), Integer, [Integer]) ->
  Var ->
  Maybe (DataCon, Integer)
compareVariableWithDataConFields node variable =
  case node of
    ((exp, likelihood), id, _) ->
      case exp of
        DataConE loc dcon args ->
          let variables = [var | VarE var <- args]
              results = P.map (variable ==) variables
              maybeIndex = L.elemIndex True results
           in case maybeIndex of
                Nothing -> Nothing
                Just val -> Just (dcon, P.toInteger val)
        _ -> Nothing

-- | Return the freeVariables bound by an expression in Order
freeVarsInOrder :: (PreExp e l d) -> [Var]
freeVarsInOrder exp =
  case exp of
    DataConE loc dcon args -> []
    VarE var -> [var]
    LitE val -> []
    CharE char -> []
    FloatE val -> []
    LitSymE var -> [var]
    AppE f locs args ->
      let var_list_list = P.map (freeVarsInOrder) args
          var_list = L.concat var_list_list
       in var_list
    PrimAppE f args ->
      let var_list_list = P.map (freeVarsInOrder) args
          var_list = L.concat var_list_list
       in var_list
    LetE (v, loc, ty, rhs) bod -> freeVarsInOrder rhs
    CaseE scrt mp ->
      (freeVarsInOrder scrt)
        ++ ( L.concat
               ( L.map
                   ( \(_, vlocs, expr) ->
                       let (vars, _) = P.unzip vlocs
                           freeVarsExp = freeVarsInOrder expr
                           newVars = freeVarsExp ++ vars
                        in newVars
                   )
                   mp
               )
           )
    IfE a b c ->
      (freeVarsInOrder a) ++ (freeVarsInOrder b) ++ (freeVarsInOrder c)
    MkProdE xs ->
      let var_list_list = P.map (freeVarsInOrder) xs
          var_list = L.concat var_list_list
       in var_list
    ProjE i e -> error "freeVarsInOrder: TODO ProjE"
    TimeIt e ty b -> error "freeVarsInOrder: TODO TimeIt"
    WithArenaE v e -> error "freeVarsInOrder: TODO WithArenaE"
    SpawnE f locs args -> error "freeVarsInOrder: TODO SpawnE"
    SyncE -> error "freeVarsInOrder: TODO SyncE"
    Ext _ -> error "freeVarsInOrder: TODO Ext"
    MapE {} -> error "freeVarsInOrder: TODO MapE"
    FoldE {} -> error "freeVarsInOrder: TODO FoldE"

removeDuplicates :: (Eq a) => [a] -> [a]
removeDuplicates list =
  case list of
    [] -> []
    a : as -> a : removeDuplicates (P.filter (/= a) as)

-- | From a given graph generate the Field ordering subgraph.
-- | A subgraph that only contains Fields from the dataCons as Vertices.
-- | Edges amongst vertices amount to the READ ACCESS Patterns amongs the fields of the DataCon.
-- | For now, we only cares about read <-> read dependencies.

-- | RETURN: an edge list and corresponding weight of the the edges
-- | Edge: a tuple from vertex to vertex, left dominates right.

-- | TODO: any FIXMEs in the function.

-- | a.) Multiple datacon fields read in the same expression.
-- | Since this will be run after flatten, it is safe to assume that only possibly a maximum of two variables can be read in one let binding.
-- | Except function calls! where more than two fields can be passed as arguments.
evaluateExpressionFieldGraph ::
  Maybe (DataCon, Integer) ->
  (G.Vertex -> (((PreExp e l d), Integer), Integer, [Integer])) ->
  (Integer -> Maybe G.Vertex) ->
  [(((PreExp e l d), Integer), Integer, [Integer])] ->
  [(((PreExp e l d), Integer), Integer, [Integer])] ->
  VariableMap ->
  DataCon ->
  [Var] ->
  [Integer] ->
  Integer ->
  [((Integer, Integer), Integer)]
evaluateExpressionFieldGraph currField nodeFromVertex vertexFromNode graph xs map datacon freeVars successors likelihood =
  case currField of
    Nothing ->
      let fromDataCon' =
            P.map
              (\v -> M.findWithDefault Nothing v map)
              (removeDuplicates freeVars)
          justDcons = [Just x | Just x <- fromDataCon']
          fromDataCon'' =
            if P.null justDcons
              then [Nothing]
              else justDcons
       in case fromDataCon'' of
            [a] ->
              case a of
                Nothing ->
                  []
                    ++ constructFieldGraph
                      Nothing
                      nodeFromVertex
                      vertexFromNode
                      graph
                      xs
                      map
                      datacon
                Just (dcon, id) ->
                  case (dcon == datacon) of
                    True ->
                      let succ' = Mb.catMaybes $ P.map vertexFromNode successors
                          succVertices = P.map nodeFromVertex succ'
                          succExp = P.map (\x -> (fst . fst3) x) succVertices
                          succprob = P.map (\x -> (snd . fst3) x) succVertices
                          {- list of list, where each list stores variables -}
                          succDataCon =
                            P.map
                              ( \x ->
                                  findFieldInDataConFromVariableInExpression
                                    x
                                    graph
                                    map
                                    datacon
                              )
                              succExp
                          {- list of tuples, where each tuple == ([(dcon, id), ... ], likelihood)    -}
                          succDataCon' =
                            P.zipWith (\x y -> (x, y)) succDataCon succprob
                          newEdges =
                            P.concat $
                              P.map
                                ( \x ->
                                    case x of
                                      (varsl, prob) ->
                                        P.map (\y -> ((id, snd y), prob)) varsl
                                )
                                succDataCon'
                       in case newEdges of
                            [] ->
                              case successors of
                                [] ->
                                  []
                                    ++ constructFieldGraph
                                      Nothing
                                      nodeFromVertex
                                      vertexFromNode
                                      graph
                                      xs
                                      map
                                      datacon
                                _ ->
                                  newEdges
                                    ++ constructFieldGraph
                                      (Just (dcon, id))
                                      nodeFromVertex
                                      vertexFromNode
                                      graph
                                      xs
                                      map
                                      datacon
                            _ ->
                              newEdges
                                ++ constructFieldGraph
                                  Nothing
                                  nodeFromVertex
                                  vertexFromNode
                                  graph
                                  xs
                                  map
                                  datacon
                    _ ->
                      []
                        ++ constructFieldGraph
                          currField
                          nodeFromVertex
                          vertexFromNode
                          graph
                          xs
                          map
                          datacon
            _ ->
              error
                "evaluateExpressionFieldGraph: More than one variable from DataCon in a let binding not modelled into Field dependence graph yet!"
    Just (dcon, pred) ->
      let fromDataCon' =
            P.map
              (\v -> M.findWithDefault Nothing v map)
              (removeDuplicates freeVars)
          justDcons = [Just x | Just x <- fromDataCon']
          fromDataCon'' =
            if P.null justDcons
              then [Nothing]
              else justDcons
       in case fromDataCon'' of
            [a] ->
              case a of
                Nothing ->
                  let succ' = Mb.catMaybes $ P.map vertexFromNode successors
                      succVertices = P.map nodeFromVertex succ'
                      succExp = P.map (\x -> (fst . fst3) x) succVertices
                      succprob = P.map (\x -> (snd . fst3) x) succVertices
                      {- list of list, where each list stores variables -}
                      succDataCon =
                        P.map
                          ( \x ->
                              findFieldInDataConFromVariableInExpression
                                x
                                graph
                                map
                                datacon
                          )
                          succExp
                      {- list of tuples, where each tuple == ([(dcon, id), ... ], likelihood)    -}
                      succDataCon' =
                        P.zipWith (\x y -> (x, y)) succDataCon succprob
                      newEdges =
                        P.concat $
                          P.map
                            ( \x ->
                                case x of
                                  (varsl, prob) ->
                                    P.map (\y -> ((pred, snd y), prob)) varsl
                            )
                            succDataCon'
                   in case newEdges of
                        [] ->
                          case successors of
                            [] ->
                              []
                                ++ constructFieldGraph
                                  Nothing
                                  nodeFromVertex
                                  vertexFromNode
                                  graph
                                  xs
                                  map
                                  datacon
                            _ ->
                              newEdges
                                ++ constructFieldGraph
                                  (Just (dcon, pred))
                                  nodeFromVertex
                                  vertexFromNode
                                  graph
                                  xs
                                  map
                                  datacon
                        _ ->
                          newEdges
                            ++ constructFieldGraph
                              Nothing
                              nodeFromVertex
                              vertexFromNode
                              graph
                              xs
                              map
                              datacon
                Just (dcon', id') ->
                  case (dcon' == datacon) of
                    True ->
                      let edges = [((pred, id'), likelihood)]
                          succ' = Mb.catMaybes $ P.map vertexFromNode successors
                          succVertices = P.map nodeFromVertex succ'
                          succExp = P.map (\x -> (fst . fst3) x) succVertices
                          succprob = P.map (\x -> (snd . fst3) x) succVertices
                          succDataCon =
                            P.map
                              ( \x ->
                                  findFieldInDataConFromVariableInExpression
                                    x
                                    graph
                                    map
                                    datacon
                              )
                              succExp
                          succDataCon' =
                            P.zipWith (\x y -> (x, y)) succDataCon succprob
                          newEdges =
                            P.concat $
                              P.map
                                ( \x ->
                                    case x of
                                      (varsl, prob) ->
                                        P.map (\y -> ((pred, snd y), prob)) varsl
                                )
                                succDataCon'
                       in newEdges
                            ++ edges
                            ++ constructFieldGraph
                              Nothing
                              nodeFromVertex
                              vertexFromNode
                              graph
                              xs
                              map
                              datacon
                    _ ->
                      []
                        ++ constructFieldGraph
                          currField
                          nodeFromVertex
                          vertexFromNode
                          graph
                          xs
                          map
                          datacon
            _ ->
              error
                "evaluateExpressionFieldGraph: More than one variable from DataCon in a let binding not modelled into Field dependence graph yet!"

constructFieldGraph ::
  Maybe (DataCon, Integer) ->
  (G.Vertex -> (((PreExp e l d), Integer), Integer, [Integer])) ->
  (Integer -> Maybe G.Vertex) ->
  [(((PreExp e l d), Integer), Integer, [Integer])] ->
  [(((PreExp e l d), Integer), Integer, [Integer])] ->
  VariableMap ->
  DataCon ->
  [((Integer, Integer), Integer)]
constructFieldGraph currField nodeFromVertex vertexFromNode graph progress map datacon =
  case progress of
    [] -> []
    x : xs ->
      let ((exp, likelihood), id'', successors) = x
       in case exp of
            LitE val ->
              case successors of
                [] ->
                  constructFieldGraph
                      Nothing
                      nodeFromVertex
                      vertexFromNode
                      graph
                      xs
                      map
                      datacon
                _ ->
                  constructFieldGraph
                      currField
                      nodeFromVertex
                      vertexFromNode
                      graph
                      xs
                      map
                      datacon
            CharE char ->
              case successors of
                [] ->
                  []
                    ++ constructFieldGraph
                      Nothing
                      nodeFromVertex
                      vertexFromNode
                      graph
                      xs
                      map
                      datacon
                _ ->
                  []
                    ++ constructFieldGraph
                      currField
                      nodeFromVertex
                      vertexFromNode
                      graph
                      xs
                      map
                      datacon
            FloatE val ->
              case successors of
                [] ->
                  []
                    ++ constructFieldGraph
                      Nothing
                      nodeFromVertex
                      vertexFromNode
                      graph
                      xs
                      map
                      datacon
                _ ->
                  []
                    ++ constructFieldGraph
                      currField
                      nodeFromVertex
                      vertexFromNode
                      graph
                      xs
                      map
                      datacon
            DataConE loc dcon args ->
              case successors of
                [] ->
                  []
                    ++ constructFieldGraph
                      Nothing
                      nodeFromVertex
                      vertexFromNode
                      graph
                      xs
                      map
                      datacon
                _ ->
                  constructFieldGraph
                      currField
                      nodeFromVertex
                      vertexFromNode
                      graph
                      xs
                      map
                      datacon
            VarE var ->
              evaluateExpressionFieldGraph
                currField
                nodeFromVertex
                vertexFromNode
                graph
                xs
                map
                datacon
                [var]
                successors
                likelihood
            LitSymE var ->
              evaluateExpressionFieldGraph
                currField
                nodeFromVertex
                vertexFromNode
                graph
                xs
                map
                datacon
                [var]
                successors
                likelihood
            LetE (v, loc, ty, rhs) bod ->
              evaluateExpressionFieldGraph
                currField
                nodeFromVertex
                vertexFromNode
                graph
                xs
                map
                datacon
                (freeVarsInOrder rhs)
                successors
                likelihood
            AppE f locs args ->
              evaluateExpressionFieldGraph
                currField
                nodeFromVertex
                vertexFromNode
                graph
                xs
                map
                datacon
                (freeVarsInOrder exp)
                successors
                likelihood
            PrimAppE f args ->
              evaluateExpressionFieldGraph
                currField
                nodeFromVertex
                vertexFromNode
                graph
                xs
                map
                datacon
                (freeVarsInOrder exp)
                successors
                likelihood
            MkProdE xss ->
              evaluateExpressionFieldGraph
                currField
                nodeFromVertex
                vertexFromNode
                graph
                xs
                map
                datacon
                (freeVarsInOrder exp)
                successors
                likelihood
            ProjE i e -> error "constructFieldGraph: TODO ProjE"
            TimeIt e ty b -> error "constructFieldGraph: TODO TimeIt"
            WithArenaE v e -> error "constructFieldGraph: TODO WithArenaE"
            SpawnE f locs args -> error "constructFieldGraph: TODO SpawnE"
            SyncE -> error "constructFieldGraph: TODO SyncE"
            Ext _ -> error "constructFieldGraph: TODO Ext"
            MapE {} -> error "constructFieldGraph: TODO MapE"
            FoldE {} -> error "constructFieldGraph: TODO FoldE"
            _ -> error "not expected"

-- | From an expression provided, Recursively find all the variables that come from a DataCon expression, that is, are fields in a DataConE.
findFieldInDataConFromVariableInExpression ::
  (PreExp e l d) ->
  [(((PreExp e l d), Integer), Integer, [Integer])] ->
  VariableMap ->
  DataCon ->
  [(DataCon, Integer)]
findFieldInDataConFromVariableInExpression exp graph map datacon =
  case exp of
    VarE var ->
      let fromDataCon = M.findWithDefault Nothing var map
       in case fromDataCon of
            Nothing -> []
            Just (dcon, id') ->
              if dcon == datacon
                then [(dcon, id')]
                else []
    LitSymE var ->
      let fromDataCon = M.findWithDefault Nothing var map
       in case fromDataCon of
            Nothing -> []
            Just (dcon, id') ->
              if dcon == datacon
                then [(dcon, id')]
                else []
    LetE (v, loc, ty, rhs) bod ->
      let freeVars = freeVarsInOrder rhs
          fromDataCon = P.map (\v -> M.findWithDefault Nothing v map) freeVars
          removeMaybe = Mb.catMaybes fromDataCon
          newDatacons =
            [ if dcon == datacon
                then Just (dcon, id')
                else Nothing
              | (dcon, id') <- removeMaybe
            ]
          newDatacons' = Mb.catMaybes newDatacons
       in newDatacons'
    AppE f locs args ->
      let freeVars = freeVarsInOrder exp
          fromDataCon = P.map (\v -> M.findWithDefault Nothing v map) freeVars
          removeMaybe = Mb.catMaybes fromDataCon
          newDatacons =
            [ if dcon == datacon
                then Just (dcon, id')
                else Nothing
              | (dcon, id') <- removeMaybe
            ]
          newDatacons' = Mb.catMaybes newDatacons
       in newDatacons'
    PrimAppE f args ->
      let freeVars = freeVarsInOrder exp
          fromDataCon = P.map (\v -> M.findWithDefault Nothing v map) freeVars
          removeMaybe = Mb.catMaybes fromDataCon
          newDatacons =
            [ if dcon == datacon
                then Just (dcon, id')
                else Nothing
              | (dcon, id') <- removeMaybe
            ]
          newDatacons' = Mb.catMaybes newDatacons
       in newDatacons'
    LitE val -> []
    CharE char -> []
    FloatE val -> []
    DataConE loc dcon args -> []
    MkProdE xss ->
      let freeVars = freeVarsInOrder exp
          fromDataCon = P.map (\v -> M.findWithDefault Nothing v map) freeVars
          removeMaybe = Mb.catMaybes fromDataCon
          newDatacons =
            [ if dcon == datacon
                then Just (dcon, id')
                else Nothing
              | (dcon, id') <- removeMaybe
            ]
          newDatacons' = Mb.catMaybes newDatacons
       in newDatacons'
    ProjE i e -> error "findFieldInDataConFromVariableInExpression: TODO ProjE"
    TimeIt e ty b ->
      error "findFieldInDataConFromVariableInExpression: TODO TimeIt"
    WithArenaE v e ->
      error "findFieldInDataConFromVariableInExpression: TODO WithArenaE"
    SpawnE f locs args ->
      error "findFieldInDataConFromVariableInExpression: TODO SpawnE"
    SyncE -> error "findFieldInDataConFromVariableInExpression: TODO SyncE"
    Ext _ -> error "findFieldInDataConFromVariableInExpression: TODO Ext"
    MapE {} -> error "findFieldInDataConFromVariableInExpression: TODO MapE"
    FoldE {} -> error "findFieldInDataConFromVariableInExpression: TODO FoldE"
