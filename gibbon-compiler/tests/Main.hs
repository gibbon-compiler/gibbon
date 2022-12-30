{-# LANGUAGE TemplateHaskell #-}

-- |

module Main where

-- |
import Data.Word (Word8)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH


import qualified Data.Map as M

import Gibbon.L4.Syntax hiding (Prog (..), Ty (..))
import Gibbon.L2.Syntax (Multiplicity(..))
import qualified Gibbon.L4.Syntax as T

-- |
import RouteEnds
import InferEffects
import InferRegionScope
import Unariser
import AddRAN
import L1.Typecheck
import L1.Interp
import L2.Typecheck
import L2.Interp
-- import L0.Specialize
import InferLocations

main :: IO ()
main = defaultMain allTests
  where allTests = testGroup "All"
                   [ tests
                   , addRANTests
                   , routeEnds2Tests
                   , inferLocations2Tests
                   , inferEffects2Tests
                   , inferRegScopeTests
                   , unariser2Tests
                   -- , l2TypecheckerTests
                   , l1TypecheckerTests
                   , l1InterpTests
                   , l2InterpTests
                   -- , specializeTests
                   ]

tests :: TestTree
tests = $(testGroupGenerator)
