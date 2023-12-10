module Gibbon.Passes.DefinitionUseChains
  ( progToVEnv
  , generateDefUseChainsFunction
  , DefUseChainsFunctionMap(..)
  ) where


-- Gibbon imports
import           Gibbon.Common
import           Gibbon.Language
import           Gibbon.Language.Syntax

import           Control.Monad                  as Monad
import           Data.Graph                     as G
import           Data.List                      as L
import           Data.Map                       as M
import           Data.Maybe                     as Maybe
import           Data.Set                       as S


-- haskell imports
import           Prelude                        as P
import           Text.PrettyPrint.GenericPretty


-- | A Map storing a function to the data flow graph that is Definition Use chains
-- | Type definition
-- | Outer Map Definition
-- | Key type Var == Function name
-- | Value type == Triple storing graph and graph associated functions. See Data.Contatiners
-- | Graph Edge == (Var, ex, (TyOf ex)), i.e., variable that's assigned, the assignment expression (polymorphic to IR), and type of the Variable.
-- | key in the Graph = ex, The expression (polymorphic IR expression) is the key itself
type DefUseChainsFunctionMap ex
   = M.Map Var ( G.Graph
               , G.Vertex -> ((Var, ex, (TyOf ex)), ex, [ex])
               , ex -> Maybe G.Vertex)

progToVEnv ::
     (FreeVars (e l d), Ord l, Ord d, Ord (e l d), Out d, Out l)
  => Prog (PreExp e l d)
  -> Env2 (TyOf (PreExp e l d))
progToVEnv p@Prog {ddefs, fundefs, mainExp} =
  case mainExp of
    Just (exp, ty) ->
      unionEnv2 (unionEnv2 initialEnv extendedVEnv) (getExpTyEnv emptyEnv2 exp)
    Nothing -> error "progToVEnv : No main expression found!"
  where
    initialEnv   = progToEnv p
    extendedVEnv = unionEnv2s (L.map (getFunTyEnv initialEnv) (M.elems fundefs))
    getFunTyEnv env f@FunDef {funName, funBody, funTy, funArgs} =
      getExpTyEnv env funBody
    getExpTyEnv env exp =
      case exp of
        DataConE loc dcon args -> unionEnv2s (L.map (getExpTyEnv env) args)
        VarE {} -> emptyEnv2
        LitE {} -> emptyEnv2
        CharE {} -> emptyEnv2
        FloatE {} -> emptyEnv2
        LitSymE {} -> emptyEnv2
        AppE f locs args -> unionEnv2s (L.map (getExpTyEnv env) args)
        PrimAppE f args -> unionEnv2s (L.map (getExpTyEnv env) args)
        LetE (v, loc, ty, rhs) bod -> extendVEnv v ty env
                                        -- a == DataCon
                                        -- b == [(Var, loc)]
                                        -- c == Case Body
        CaseE scrt mp ->
          unionEnv2s $
          P.map
            (\(a, b, c) ->
               let tys = lookupDataCon ddefs a
                   b' = L.map fst b
                   env' = extendsVEnv (M.fromList (zip b' tys)) env
                in env')
            mp
        IfE a b c ->
          let expEnva = getExpTyEnv env a
              expEnvb = getExpTyEnv env b
              expEnvc = getExpTyEnv env c
           in unionEnv2s $ [expEnva, expEnvb, expEnvc]
        MkProdE xs -> unionEnv2s (L.map (getExpTyEnv env) xs)
        ProjE i e -> error "getExpTyEnv: TODO ProjE"
        TimeIt e ty b -> error "getExpTyEnv: TODO TimeIt"
        WithArenaE v e -> error "getExpTyEnv: TODO WithArenaE"
        SpawnE f locs args -> error "getExpTyEnv: TODO SpawnE"
        SyncE -> error "getExpTyEnv: TODO SyncE"
        Ext _ -> error "getExpTyEnv: TODO Ext"
        MapE {} -> error "getExpTyEnv: TODO MapE"
        FoldE {} -> error "getExpTyEnv: TODO FoldE"

generateDefUseChainsFunction ::
     (FreeVars (e l d), Ord l, Ord d, Ord (e l d), Out d, Out l)
  => Env2 (TyOf (PreExp e l d))
  -> FunDef (PreExp e l d)
  -> DefUseChainsFunctionMap (PreExp e l d)
generateDefUseChainsFunction env f@FunDef {funName, funBody, funTy, funArgs} =
  let edgeList = generateDefUseChainsFunBody env funBody
      (graph, nodeFromVertex, vertexFromKey) = G.graphFromEdges edgeList
   in dbgTraceIt
        (sdoc edgeList)
        dbgTraceIt
        ("\n")
        M.insert
        funName
        (graph, nodeFromVertex, vertexFromKey)
        M.empty

generateDefUseChainsExp ::
     (FreeVars (e l d), Ord l, Ord d, Ord (e l d), Out d, Out l)
  => Env2 (TyOf (PreExp e l d))
  -> Var
  -> (PreExp e l d)
  -> DefUseChainsFunctionMap (PreExp e l d)
generateDefUseChainsExp env key expr =
  let edgeList = generateDefUseChainsFunBody env expr
      (graph, nodeFromVertex, vertexFromKey) = G.graphFromEdges edgeList
   in dbgTraceIt
        (sdoc edgeList)
        dbgTraceIt
        ("\n")
        M.insert
        key
        (graph, nodeFromVertex, vertexFromKey)
        M.empty

generateDefUseChainsFunBody ::
     (FreeVars (e l d), Ord l, Ord d, Ord (e l d), Out d, Out l)
  => Env2 (TyOf (PreExp e l d))
  -> (PreExp e l d)
  -> [( (Var, (PreExp e l d), (TyOf (PreExp e l d)))
      , (PreExp e l d)
      , [(PreExp e l d)])]
generateDefUseChainsFunBody env exp =
  case exp of
    DataConE loc dcon args -> P.concatMap (generateDefUseChainsFunBody env) args
    VarE {} -> []
    LitE {} -> []
    CharE {} -> []
    FloatE {} -> []
    LitSymE {} -> []
    AppE f locs args -> P.concatMap (generateDefUseChainsFunBody env) args
    PrimAppE f args -> P.concatMap (generateDefUseChainsFunBody env) args
    LetE (v, loc, ty, rhs) bod ->
      let successors = getDefUseChainsVar v bod False
          currExpKey = LetE (v, loc, ty, rhs) $ VarE v
          currNode = (v, currExpKey, ty)
          recurseBod = (generateDefUseChainsFunBody env) bod
       in [(currNode, currExpKey, successors)] ++ recurseBod
    -- a == DataCon
    -- b == [(Var, loc)]
    -- c == Case Body
    CaseE scrt mp ->
      let edges =
            P.concatMap
              (\(a, b, c) ->
                 let e =
                       P.concatMap
                         (\(v, _) ->
                            let successors = getDefUseChainsVar v c False
                                currExpKey =
                                  DataConE _ a (P.map (\(v', _) -> VarE v') b)
                                currNode = (v, currExpKey, (lookupVEnv v env))
                             in [(currNode, currExpKey, successors)])
                         b
                     e' = (generateDefUseChainsFunBody env) c
                  in e ++ e')
              mp
       in edges
    IfE a b c ->
      let definitionsCond = (generateDefUseChainsFunBody env) a
          thenBody = (generateDefUseChainsFunBody env) b
          elseBody = (generateDefUseChainsFunBody env) c
       in definitionsCond ++ thenBody ++ elseBody
    MkProdE xs -> P.concatMap (generateDefUseChainsFunBody env) xs
    _ ->
      error
        "generateDefUseChainsFunBody: Encountered expression which is not implemented yet!"

getDefUseChainsVar ::
     (FreeVars (e l d), Ord l, Ord d, Ord (e l d), Out d, Out l)
  => Var
  -> (PreExp e l d)
  -> Bool
  -> [(PreExp e l d)]
getDefUseChainsVar var exp isReDefined =
  case exp of
    DataConE loc dcon args ->
      case isReDefined of
        True -> []
        False ->
          let freeVars = S.unions $ L.map gFreeVars args
           in if (S.member var freeVars)
                then [DataConE loc dcon args]
                else []
                        -- Program is in ANF, so we can assume that its flattned
                        -- so args is not going to be a complex nested expression.
                        -- check if var is in freeVars
                        -- If yes, add then return [exp1]
                        -- If no, then return []
    VarE {} -> []
    LitE {} -> []
    CharE {} -> []
    FloatE {} -> []
    LitSymE {} -> []
    AppE f locs args ->
      case isReDefined of
        True -> []
        False ->
          let freeVars = S.unions $ L.map gFreeVars args
           in if (S.member var freeVars)
                then [AppE f locs args]
                else []
                        -- check if var is in freeVars
                        -- If yes, then return [exp1]
                        -- If no, then return []
    PrimAppE f args ->
      case isReDefined of
        True -> []
        False ->
          let freeVars = S.unions $ L.map gFreeVars args
           in if (S.member var freeVars)
                then [PrimAppE f args]
                else []
                        -- check if var is in freeVars
                        -- If yes, then return [exp1]
                        -- If no, then return []
    LetE (v, loc, ty, rhs) bod ->
      case isReDefined of
        True -> []
        False ->
          let freeVars = gFreeVars rhs
              usedInRhs =
                if (S.member var freeVars)
                  then True
                  else False
              isReDefined =
                if (var == v)
                  then True
                  else False
           in if usedInRhs
                then let expr = [LetE (v, loc, ty, rhs) $ (VarE v)]
                         moreExpr = getDefUseChainsVar var bod isReDefined
                      in expr ++ moreExpr
                else getDefUseChainsVar var bod False
                            -- check if var is in freeVars
                            -- equality test on v and var
                            -- If yes, then, recurse on bod, pass result of equality check
                            -- add LetE (v,loc,ty,rhs) $ (VarE v) to returned val
                            -- return new value
    CaseE scrt mp ->
      case isReDefined of
        True -> []
        -- see if the variable is used in scrt
        False ->
          case scrt of
            VarE v ->
              if (v == var)
                then let expr = [CaseE scrt []]
                            -- Here making as assumption that the variable is not shadowed by
                            -- a case binding in b == [(Var, loc)]
                         moreExpr =
                           P.concatMap
                             (\(_, _, c) -> getDefUseChainsVar var c False)
                             mp
                      in expr ++ moreExpr
                else let exprs =
                           P.concatMap
                             (\(_, _, c) -> getDefUseChainsVar var c False)
                             mp
                      in exprs
            _ -> error "getDefUseChainsVar: CaseE did not expect case: "
    IfE a b c ->
      case isReDefined of
        True -> []
        False ->
          let freeVarsA = gFreeVars a
           in if (S.member var freeVarsA)
                then let expra = [a]
                         exprsb = getDefUseChainsVar var b False
                         exprsc = getDefUseChainsVar var c False
                      in expra ++ exprsb ++ exprsc
                else let exprsb = getDefUseChainsVar var b False
                         exprsc = getDefUseChainsVar var c False
                      in exprsb ++ exprsc
    MkProdE xs ->
      case isReDefined of
        True -> []
        False ->
          let freeVars = S.unions $ L.map gFreeVars xs
           in if (S.member var freeVars)
                then [MkProdE xs]
                else []
                        -- I don't think there is a need to recurse on xs
                        -- since it would be in A-normal form at this point.
                        -- Check?
    ProjE i e -> error "getDefUseChainsVar: TODO ProjE"
    TimeIt e ty b -> error "getDefUseChainsVar: TODO TimeIt"
    WithArenaE v e -> error "getDefUseChainsVar: TODO WithArenaE"
    SpawnE f locs args -> error "getDefUseChainsVar: TODO SpawnE"
    SyncE -> error "getDefUseChainsVar: TODO SyncE"
    MapE {} -> error "getDefUseChainsVar: TODO MapE"
    FoldE {} -> error "getDefUseChainsVar: TODO FoldE"
    Ext _ -> error "getDefUseChainsVar: TODO Ext"
