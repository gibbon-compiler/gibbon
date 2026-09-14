-- | Reading the cursorized calling convention off a function.
--
-- See Note [The cursorized calling convention] in "Gibbon.Language.Syntax":
-- cursorization records one 'AbiRole' per formal, and everything that needs to
-- know which cursor array is the output reads it from here.  Nothing in the
-- compiler may recover that from argument order instead -- four passes used to,
-- independently, and a reordering in cursorization would have silently swapped
-- input and output roles in all of them while every type still checked.
--
-- Every function here fails closed.  A function with no recorded convention is
-- one cursorization did not produce, so it has no cursorized ABI to read and
-- the answer is 'Nothing', never a guess.
module Gibbon.L3.Abi
  ( CursorPairShape(..)
  , abiCursorArrayAt
  , abiUniquePosition
  , soaOutputCursorShape
  , soaInputCursorShapes
  ) where

import Control.Monad (guard)

import Gibbon.Language
import Gibbon.L3.Syntax

-- | An (ends, cursors) argument pair addressing one SoA value, plus the number
-- of buffers that value has.
data CursorPairShape = CursorPairShape
  { cpsLen :: Int
  , cpsEndArgIx :: Int
  , cpsCurArgIx :: Int
  }
  deriving (Eq, Ord, Show)

-- | The number of buffers in the cursor array at this formal position, if the
-- formal is a cursor array at all.
abiCursorArrayAt :: [Ty3] -> Int -> Maybe Int
abiCursorArrayAt tys ix =
  case drop ix tys of
    CursorArrayTy n : _ | ix >= 0 -> Just n
    _ -> Nothing

-- | The one formal with this role, or 'Nothing' when there is not exactly one.
--
-- Two formals sharing a role is a shape none of these readers can address
-- unambiguously -- a two-packed-input traversal has two input ends -- so it is
-- declined rather than resolved by picking one.
abiUniquePosition :: AbiRole -> [AbiRole] -> Maybe Int
abiUniquePosition role roles =
  case abiPositions role roles of
    [ix] -> Just ix
    _ -> Nothing

-- | The (output ends, output cursors) pair of a cursorized producer.
soaOutputCursorShape :: FunDef3 -> Maybe CursorPairShape
soaOutputCursorShape FunDef{funTy = (tys, _), funMeta} = do
  roles <- funCursorAbi funMeta
  endIx <- abiUniquePosition AbiOutEnd roles
  curIx <- abiUniquePosition AbiOutCur roles
  n1 <- abiCursorArrayAt tys endIx
  n2 <- abiCursorArrayAt tys curIx
  guard (n1 == n2 && n1 > 1)
  pure (CursorPairShape n1 endIx curIx)

-- | The (input ends, input cursors) pairs a cursorized consumer is handed.
--
-- A list because a traversal may read more than one packed input; each pair is
-- one input value.
soaInputCursorShapes :: FunDef3 -> [CursorPairShape]
soaInputCursorShapes FunDef{funTy = (tys, _), funMeta} =
  case funCursorAbi funMeta of
    Nothing -> []
    Just roles ->
      [ CursorPairShape n1 endIx curIx
      | endIx <- abiPositions AbiInEnd roles
      , curIx <- abiPositions AbiInCur roles
      , Just n1 <- [abiCursorArrayAt tys endIx]
      , Just n2 <- [abiCursorArrayAt tys curIx]
      , n1 == n2
      , n1 > 1
      ]
