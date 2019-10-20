-- | Aggressive dead code elimination.  No regard for termination,
-- effects, or partiality.

-- [Populated with duplicated code from InlinePacked]

module Gibbon.Passes.ShakeTree
    (shakeTree) where

import Data.Loc
import Prelude hiding (exp)
import qualified Data.Map as M
import qualified Data.Set as S

import Gibbon.Common (PassM, dbgTrace)
import Gibbon.L1.Syntax
import Gibbon.L3.Syntax


-- | Drop all unreferenced let-bindings.
shakeTree :: Prog3 -> PassM Prog3
shakeTree prg@Prog{fundefs,mainExp} = return $
  prg { fundefs = M.map fd fundefs
      , mainExp = case mainExp of
                    Nothing      -> Nothing
                    (Just (e,t)) -> Just (shakeTreeExp e, t)
      }
 where
   fd f@FunDef{funBody} = f { funBody = shakeTreeExp funBody }

shakeTreeExp :: L Exp3 -> L Exp3
shakeTreeExp = go
  where

  go :: L Exp3 -> L Exp3
  go (L p e0) = L p $
   -- dbgTrace 5 ("Inline, processing with env:\n "++sdoc env++"\n exp: "++sdoc e0) $
   case e0 of

    (LetE (v,locs,t,rhs) bod) ->
        let bod' = go bod
            fv   = gFreeVars bod'
        in
        if S.member v fv || hasEffect rhs
        then LetE (v,locs,t, go rhs) bod'
        else dbgTrace 4 (" [shakeTreeExp] dropping binding: "++show (v,t,rhs))$ unLoc bod'

    (VarE v)           -> VarE v
    (LitE i)           -> LitE i
    (LitSymE v)        -> LitSymE v
    (AppE f locs es)   -> AppE f locs $ map go es
    (PrimAppE pr es)   -> PrimAppE pr $ map go es
    (IfE e1 e2 e3)     -> IfE (go e1) (go e2) (go e3)

    (ProjE i e)  -> ProjE i $ go e
    (MkProdE es) -> MkProdE $ map (go) es

    -- We don't rename field binders with to/from witness:
    (CaseE e mp) -> let mp' = map dorhs mp
                        dorhs (c,args,ae) =
                            (c,args,go ae)
                    in CaseE (go e) mp'

    (DataConE c loc es) -> DataConE c loc $ map (go) es
    (TimeIt e t b)      -> TimeIt (go e) t b
    (MapE (v,t,e') e)   -> MapE (v,t,go e') (go e)
    (FoldE (v1,t1,e1) (v2,t2,e2) e3) ->
         FoldE (v1,t1,go e1) (v2,t2,go e2)
               (go e3)

    -- Assume that these are trivial, and always have effects
    Ext _ext -> e0




-- | On cursors we have affine types rather than linear.  Thus, unfortunately, we don't
-- have the invariant that the cursors returned by WriteTag are actually USED.  Thus we
-- cannot use dataflow alone to determine what must be kept.
--
-- This contains details that are specific to this pass, which is
-- post-cursorize.  It's not really a good general definition of "hasEffect".
hasEffect :: L Exp3 -> Bool
hasEffect (L _ rhs) =
    -- Trivials have been inlined, but we're still flat-ish:
    case rhs of
      VarE _ -> False
      LitE _ -> False
      LitSymE _ -> False

      -- These might have effects on output cursors, but the output cursors aren't used
      -- again!  We need to tie the knot in dataflow dependencies, making the start (value)
      -- depend on the end (final cursor).
      AppE _ _ _ -> True  -- For now, don't drop.

      PrimAppE _ _ -> False -- No prims have effects.

      LetE (_,_,_,e1) e2 -> hasEffect e1 || hasEffect e2

      ProjE _ e    -> hasEffect e      -- Flattening should make this equivalent to "False"
      MkProdE ls   -> any hasEffect ls -- Flattening should make this equivalent to "False"

      IfE a b c -> hasEffect a || hasEffect b || hasEffect c

      CaseE _ _ -> True -- Umm, just don't drop for now. FIXME/ REVISIT THIS!

      DataConE _ _ _ -> True

      TimeIt{} -> True -- Yes, has effect of printing!

      MapE _ _ -> error "hasEffect: FIXME MapE"
      FoldE _ _ _ -> error "hasEffect: FIXME FoldE"

      -- always have effects
      Ext _ -> True

      -- oth -> error $" [shakeTrees] unexpected RHS on Let:\n "++sdoc rhs
