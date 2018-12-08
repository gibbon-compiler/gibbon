{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Gibbon.Passes.RepairProgram
  (repairProgram) where

import Data.Set as S

import Gibbon.DynFlags
import Gibbon.Common
import Gibbon.L2.Syntax
import Gibbon.L1.Syntax
import Gibbon.Passes.InferLocations (inferLocs)
import Gibbon.Passes.InferEffects   (inferEffects)
import Gibbon.Passes.RemoveCopies   (removeCopies)
import Gibbon.Passes.Flatten        (flattenL2)
import Gibbon.Passes.AddTraversals  (addTraversals)
import Gibbon.Passes.AddRAN         (addRAN,needsRAN)

--------------------------------------------------------------------------------

{- Note [Repairing programs]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

We need a program analysis that decides whether a L2 program needs to be repaired.
Why ? Because, when we pattern match on a packed value, L2 assumes that *every*
variable in that pattern is accessible. However, this is not always true.
Consider the rightmost fn (which does not traverse it's input):

   (Node [(x, loc_x), (y, loc_y)] BODY)

Here, since the input is not traversed, we won't have an end-witness for x. And we
cannot access y without it. We need to fix such programs. Effectively, what we're
looking for in this analyis is if we can unpack all the pattern matched variables
in case expressions occurring in the program. For functions, it means that either
the function should traverse it's input, or the un-reachable elements in the pattern
match must remain unused (eg. 'leftmost'). On the other hand, we always have to
repair a broken main expression (since the "unused" case won't apply).

The compiler has access to 2 program repair strategies -- dummy traversals or
random access nodes. If we're operating in gibbon1 mode, it uses the former. However,
this changes the asymptotic complexity of the functions. In gibbon2 mode, we compile
such programs to store RAN's instead. This basically allows O(1) access to any element
of a data constructor.

Also see Note [Adding dummy traversals] and Note [Adding random access nodes].

-}


-- | Add random access nodes to the program, but only where required
repairProgram :: Prog1 -> Prog2 -> PassM Prog2
repairProgram oldl1 prg = do
  isGibbon1 <- gopt Opt_Gibbon1 <$> getDynFlags

  if isGibbon1
  -- addTraversals can figure out if/where traversals are needed. So we don't have to
  -- run any 'needs*' analysis before that.
  then repairGibbon1
  else if not (S.null need_ran)
       then repairGibbon2
       else return prg

  where
    need_ran = needsRAN prg

    repairGibbon1 = do
        l2 <- addTraversals prg
        l2 <- inferEffects l2
        return l2

    repairGibbon2 = do
        l1 <- addRAN need_ran oldl1
        l2 <- inferLocs l1
        l2 <- flattenL2 l2
        l2 <- removeCopies l2
        l2 <- inferEffects l2
        return l2
