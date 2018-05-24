{-# LANGUAGE OverloadedStrings #-}
-- | Aggressive inliner to put Packed-typed expressions syntactically
-- under constructors that they flow to.

-- WARNING: DUPLICATED code from InlineTriv.hs

module Gibbon.Passes.InlinePacked
    ( inlinePacked )
    where

import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.List as L
import Gibbon.Common (SyM, Var, dbgTrace, ndoc, sdoc, lookupDataCon, DDefs)
import qualified Gibbon.L1.Syntax as L1
import Gibbon.L2.Syntax as L2
import Prelude hiding (exp)
import Gibbon.Common (Var(..), toVar, fromVar)

-- | This pass gets ready for cursorDirect by pushing tree-creating
-- expressions within the syntactic scope of data constructor
-- applications.
--
-- STARTING INVARIANTS:
--
--   (1) Variables used only as witnesses are marked, and we NEVER
--      inline Datacons into those locations.  We should already be
--      thinking of those just as pointers.
--
-- ENDING INVARIANTS:
--
--   (1) unbound variables may occur in the RHS of (LetE (_,CursorTy,_))
--       bindings, but nowwhere else.
--
--   (2) "witness" marked vars no longer occur. These markings have
--       served their purpose and are stripped.
--
--   (3) Wherever possible, (e :: PackedType) subexpressions only
--       occur inside the arguments to data constructors.  Any place
--       where this is not the case will involve either a scoped
--       region or extra copying.
--
inlinePacked :: L2.Prog2 -> SyM L2.Prog2
inlinePacked prg@L2.Prog{ddefs,fundefs,mainExp} = return $
  prg { fundefs = M.map fd fundefs
      , mainExp = case mainExp of
                    Nothing      -> Nothing
                    (Just (e,t)) -> Just (inlinePackedExp ddefs [] e, t)
      }
 where
   fd f@FunDef{funarg, funty= ArrowTy inT _ _, funbod} =
       f { funbod = inlinePackedExp ddefs
                    [(funarg, (fmap (const ()) inT, DontInline))]
                    funbod }


data InlineStatus = DontInline -- ^ Move along, nothing to see here.
--                  | DependsOn  (S.Set Var) -- ^ I'm a binding that doesn't *want* to inline,
                                           -- but I'm being drug along for the ride, because
                                           -- I depend on something else whose original binding
                                           -- was blasted away.
                  | InlineMe L1.Exp -- ^ I exist only as an expression to be inlined.

-- | 'Nothing' on the RHS indicates "not inlinable".
type InlineEnv = [(Var,(L1.Ty, InlineStatus))]

-- | Keep a map of the entire lexical environment, but only part of it
-- is inlinable. (I.e. function arguments are not.)
--
-- The policy at the moment is to inline ONLY `isConstructor`
-- bindings, and not to remove
inlinePackedExp :: DDefs L1.Ty -> InlineEnv -> L1.Exp -> L1.Exp
inlinePackedExp ddefs = exp True
  where

  -- After this pass, these markers have served their purpose and can go away:
  var :: Var -> Var
  var v | isWitnessVar v = let Just v' = fromWitnessVar v in (toVar v')
        | otherwise = v

  -- | This takes a flag indicating how aggressively to inline.  We
  -- have a special case where for end-var witnesses we don't inline as much.
  --
  -- Here the environment contains code that has NOT yet been recursively processed.
  exp :: Bool -> InlineEnv -> L1.Exp -> L1.Exp
  exp strong env e0 =
   let go = exp strong env in
   -- dbgTrace 5 ("Inline "++show strong++", processing with env:\n   "++
   --             show [v | (v,(_,Just _)) <- env]++"\n   EXP: "++show e0) $
   case e0 of
    -- Here the witness variable markers intentionally prevent inlining:
    (VarE v) -> case lookup v env of
                  Nothing -> dbgTrace 1 ("WARNING [inlinePacked] unbound variable: "++ fromVar v)$
                             VarE (var v)
                  Just (_,DontInline)  -> VarE (var v) -- Bound, but non-inlinable binding.
                  -- Here we either inline just the copies, or we inline up to `isConstructor`
                  Just (ty,InlineMe rhs)
                   | VarE _v2 <- rhs    -> keepGoing
                     -- We allow a ProjE-of-AppE idiom:
                   | ProjE _i _e <- rhs -> keepGoing
                    -- IF we're in the RHS of an end-witness, don't duplicate code:
                   | not strong -> VarE v
                    -- Finally, we don't fully inline, but rather leave *names* visible:
                   | isConstructor rhs -> NamedVal v ty keepGoing
                   | CaseE{} <- rhs    -> NamedVal v ty keepGoing
                   | IfE{}   <- rhs    -> NamedVal v ty keepGoing
                   | otherwise -> error $ "inlinePacked: internal error, should not have "
                                        ++ "this is the inlining environment:\n "++sdoc rhs
                   where
                    keepGoing = exp strong env rhs

    (LetE (v,t,rhs) bod)
       | VarE _v2   <- rhs  -> addAndGo  -- ^ We always do copy-prop.
       | not (L2.hasRealPacked t) -> keepIt
       | ProjE _ _  <- rhs  -> addAndGo

       -- DONT inline timing:
       | TimeIt{}   <- rhs  -> keepIt
       -- DONT inline file reading:
       | PrimAppE (L1.ReadPackedFile{}) _ <- rhs -> keepIt
       | isConstructor rhs -> addAndGo
       -- Otherwise we have a case or an If.  We still inline those.
       | CaseE{} <- rhs  -> addAndGo
       | IfE{}  <- rhs   -> addAndGo
       | otherwise -> error $ " [inlinePacked] unexpected Let RHS:  "++ndoc rhs
      where
        --------------------------------------------------------------
        -- NOTE: If we drag an inlined binding past a let binding that
        -- USES it in the RHS, then we have some work to do.
        --  >  let x = inlinable in
        --  >  let y = f x in ...
        --------------------------------------------------------------
        rhsFree     = L1.freeVars rhs
        usedInlined = S.intersection rhsFree (S.fromList (L.map fst env)) -- Expensive. FIXME.
        keepIt =
            if True -- S.null usedInlined -- TODO FINISHME
            then -- It's all good here, our RHS won't have any unmet dependencies:
                 LetE (var v,t, rhs') (exp strong ((v,(t,DontInline)):env) bod)
            else error $ " [inlinePacked] Cannot keep let binding in place which refers to inlined vars ("
                        ++show (S.toList usedInlined)++"): " ++show (var v, t)

        -- Don't reduce anything on the RHS yet, just add it:
        addAndGo = exp strong ((v,(t,InlineMe rhs)):env) bod -- KILL the let binding!
        -- Subtlety: a binding for an end-witness should not have
        -- computational content.  We will not inline constructors into its RHS.
        rhs' | isEndVar v = exp False env rhs
             | otherwise  = go rhs

    ------ boilerplate -------
    (LitE i)    -> LitE i
    (LitSymE v) -> LitSymE v
    (AppE f e)  -> AppE f $ go e
    (PrimAppE p es) -> PrimAppE p $ map (go) es
    (IfE e1 e2 e3) ->
         IfE (go e1) (go e2) (go e3)
    (ProjE i e) -> ProjE i $ go e
    (MkProdE es) -> MkProdE $ map (go) es
    -- We don't rename field binders with to/from witness:
    (CaseE e mp) -> let mp' = map dorhs mp
                        dorhs (c,args,ae) =
                            let tys = lookupDataCon ddefs c
                                env' = [(v,(t,DontInline)) | (v,t) <- (zip args tys)] ++ env in
                            (c,args,exp strong env' ae)
                    in CaseE (go e) mp'
    (DataConE c es) -> DataConE c $ map (go) es
    (TimeIt e t b) -> TimeIt (go e) t b
    (MapE (v,t,e') e) -> let env' = (v,(t,DontInline)) : env in
                         MapE (var v,t,go e') (exp strong env' e)
    (FoldE (v1,t1,e1) (v2,t2,e2) e3) ->
         let env' = (v1,(t1,DontInline)) :
                    (v2,(t2,DontInline)) : env in
         FoldE (var v1,t1,go e1) (var v2,t2,go e2)
               (exp strong env' e3)

-- | Is it a call that actually allocates output data?
isConstructor :: Exp -> Bool
isConstructor ex =
  case ex of
    AppE{}      -> True -- ^ Fixme, shouldn't this depend on the type?
    DataConE{} -> True
--    PrimAppE (L1.ReadPackedFile{}) _ -> True
    _ -> False
