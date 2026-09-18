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
import OutputCompareTests
import TimingOutputContract
import IntWidths
import IntWidthsPipeline
import IntWidthsCompat
import IntConversions
import IntArithmetic
import CArithModes
import InferEffects
import InferRegionScope
import Unariser
import AddRAN
import LoopifyTraversals
import LoopifyFlatTraversals
import ReorderScalarWrites
import AssignScalarCountSlots
import L3Traverse
import ScalarCountPropagation
import SelectiveBufferSharing
import VectorizeTraversals
import CodegenSimd
import CodegenInvariants
import TagSpace
import L1.Typecheck
import L1.Interp
import L2.Typecheck
import L2.Interp
-- import L0.Specialize
import InferLocations
import HoistBoundsCheck
import NonRecCursorReturns

main :: IO ()
main = defaultMain allTests
  where allTests = testGroup "All"
                   [ tests
                   , outputCompareTests
                   , timingOutputContractTests
                   , addRANTests
                   , loopifyTraversalsTests
                   , loopifyFlatTraversalsTests
                   , reorderScalarWritesTests
                   , assignScalarCountSlotsTests, scalarCountPropagationTests
                   , l3TraverseTests
                   , selectiveBufferSharingTests
                   , vectorizeTraversalsTests
                   , codegenSimdTests
                   , codegenInvariantsTests
                   , tagSpaceTests
                   , routeEnds2Tests
                   , intWidthTests
                   , intWidthPipelineTests
                   , intWidthsCompatTests
                   , intConversionsTests
                   , intArithmeticTests
                   , cArithModesTests
                   , inferLocations2Tests
                   , inferEffects2Tests
                   , inferRegScopeTests
                   , unariser2Tests
                   -- , l2TypecheckerTests
                   , l1TypecheckerTests
                   , l1InterpTests
                   , l2InterpTests
                   -- , specializeTests
                   , hoistBoundsCheckTests
                   , nonRecCursorReturnsTests
                   ]

tests :: TestTree
tests = $(testGroupGenerator)
