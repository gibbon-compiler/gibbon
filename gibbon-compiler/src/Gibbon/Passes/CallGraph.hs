module Gibbon.Passes.CallGraph
  ( generateProducerGraph
  , ProducersMap(..)
  ) where


-- Gibbon imports
import           Gibbon.Common
import           Gibbon.Language
import           Gibbon.Language.Syntax
import           Gibbon.Passes.DefinitionUseChains (generateDefUseChainsFunction,
                                                    progToVEnv)

import           Control.Monad                     as Monad
import           Data.Graph                        as G
import           Data.List                         as L
import           Data.Map                          as M
import           Data.Maybe                        as Maybe
import           Data.Set                          as S


-- haskell imports
import           Prelude                           as P
import           Text.PrettyPrint.GenericPretty


-- | A Type to store the producers of all arguments passed to a function call
-- | Outer map, maps the function name to a second map.
-- | The inner (second map) stores each variable which is the argument to the function call and its type to the function that produces the argument.
type ProducersMap ex = M.Map (Var, TyOf ex) ex

generateProducerGraph ::
     (FreeVars (e l d), Ord l, Ord d, Ord (e l d), Out d, Out l)
  => Prog (PreExp e l d)
  -> ProducersMap (PreExp e l d)
generateProducerGraph prg@Prog {ddefs, fundefs, mainExp} =
  let vEnv = progToVEnv prg
      pcMapF =
        P.map
          (\f@FunDef {funName, funBody, funTy, funArgs} ->
             generateProducerGraphExpression vEnv funBody)
          (M.elems fundefs)
   in case mainExp of
        Nothing -> M.unions pcMapF
        Just (exp, ty) ->
          let mainMap = generateProducerGraphExpression vEnv exp
           in M.unions (pcMapF ++ [mainMap])


-- Everything is flattned and in SSA Form so we can get away with just analyzing let expressions and case bindings.
generateProducerGraphExpression ::
     (FreeVars (e l d), Ord l, Ord d, Ord (e l d), Out d, Out l)
  => Env2 (TyOf (PreExp e l d))
  -> (PreExp e l d)
  -> ProducersMap (PreExp e l d)
generateProducerGraphExpression venv exp =
  case exp of
    DataConE loc dcon args ->
      let maps = P.map (generateProducerGraphExpression venv) args
       in M.unions maps
    VarE {} -> M.empty
    LitE {} -> M.empty
    CharE {} -> M.empty
    FloatE {} -> M.empty
    LitSymE {} -> M.empty
    AppE f locs args ->
      let maps = P.map (generateProducerGraphExpression venv) args
       in M.unions maps
    PrimAppE f args ->
      let maps = P.map (generateProducerGraphExpression venv) args
       in M.unions maps
    LetE (v, loc, ty, rhs) bod ->
      let vProducer = M.insert (v, ty) rhs M.empty
          map' = (generateProducerGraphExpression venv) bod
       in M.union vProducer map'
   -- a == DataCon
   -- b == [(Var, loc)]
   -- c == Case Body
    CaseE scrt mp ->
      let newMaps =
            P.map
              (\(a, b, c) ->
                 let m =
                       P.map
                         (\(var, _) ->
                            M.insert
                              (var, lookupVEnv var venv)
                              (DataConE _ a [])
                              M.empty)
                         b
                     mc = generateProducerGraphExpression venv c
                  in M.unions (m ++ [mc]))
              mp
       in M.unions newMaps
    IfE a b c ->
      let ma = generateProducerGraphExpression venv a
          mb = generateProducerGraphExpression venv b
          mc = generateProducerGraphExpression venv c
       in M.unions [ma, mb, mc]
    MkProdE xs ->
      let maps = P.map (generateProducerGraphExpression venv) xs
       in M.unions maps
    ProjE i e -> error "generateProducerGraphExpression: TODO ProjE"
    TimeIt e ty b -> error "generateProducerGraphExpression: TODO TimeIt"
    WithArenaE v e -> error "generateProducerGraphExpression: TODO WithArenaE"
    SpawnE f locs args -> error "generateProducerGraphExpression: TODO SpawnE"
    SyncE -> error "generateProducerGraphExpression: TODO SyncE"
    MapE {} -> error "generateProducerGraphExpression: TODO MapE"
    FoldE {} -> error "generateProducerGraphExpression: TODO FoldE"
    Ext _ -> error "generateProducerGraphExpression: TODO Ext"
