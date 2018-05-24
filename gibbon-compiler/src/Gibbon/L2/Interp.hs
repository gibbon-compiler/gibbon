{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

-- | Interpreter reducing L2 programs to values.

module Gibbon.L2.Interp
    () -- Instances only.
    where

import           Gibbon.Common
import           Gibbon.GenericOps(Interp, interpNoLogs, interpWithStdout)
import qualified Gibbon.L2.Syntax as L2
import           Gibbon.L1.Interp

-- | HACK: we don't have a type-level distinction for when cursors are
-- allowed in the AST.  We use L2 as a proxy for this, allowing
-- cursors whenver executing L2, even though this is a bit premature
-- in the compiler pipeline.
instance Interp L2.Prog2 where
  interpNoLogs rc p2     = interpNoLogs     rc{rcCursors=True} (L2.revertToL1 p2)
  interpWithStdout rc p2 = interpWithStdout rc{rcCursors=True} (L2.revertToL1 p2)
