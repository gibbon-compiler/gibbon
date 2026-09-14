{-# LANGUAGE TemplateHaskell #-}

-- | A datacon tag is one byte, and the space is shared.
--
-- Ordinary constructors fill from 0, their random-access variants from
-- 'ranTagBase', and the garbage collector's own tags sit at the top.  A type
-- with enough constructors runs one range into the next, and nothing
-- downstream would notice: the tag is still a tag some reader accepts, just
-- not as the constructor that was written.
module TagSpace
  ( tagSpaceTests
  ) where

import Control.Exception (ErrorCall, evaluate, try)
import qualified Data.List as L
import qualified Data.Map as M

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.TH

import Gibbon.Common
import Gibbon.Language
import Gibbon.Passes.Lower (getTagOfDataCon)

-- | A type with @n@ nullary constructors, named @K0@ .. @K<n-1>@.
manyConDDefs :: Int -> DDefs (UrTy ())
manyConDDefs n =
  M.fromList
    [ ( "Many"
      , DDef
          { tyName = "Many"
          , tyArgs = []
          , dataCons = [ ("K" ++ show i, []) | i <- [0 .. n - 1] ]
          , memLayout = Linear
          } ) ]

tagOf :: DDefs (UrTy ()) -> DataCon -> IO (Either ErrorCall Tag)
tagOf dds dcon = try (evaluate (getTagOfDataCon dds dcon))

expectRefusal :: String -> Either ErrorCall Tag -> Assertion
expectRefusal what r =
  case r of
    Right t -> assertFailure (what ++ ": expected a refusal, got tag " ++ show t)
    Left e ->
      assertBool ("unexpected message: " ++ show e)
        ("has too many constructors" `L.isInfixOf` show e)

--------------------------------------------------------------------------------

-- | The last constructor that still fits below the random-access range.
case_last_ordinary_tag_is_accepted :: Assertion
case_last_ordinary_tag_is_accepted = do
  r <- tagOf (manyConDDefs ranTagBase) ("K" ++ show (ranTagBase - 1 :: Int))
  case r of
    Right t -> t @?= fromIntegral (ranTagBase - 1 :: Int)
    Left e -> assertFailure ("expected the last in-range tag to be accepted: " ++ show e)

-- | One more, and an ordinary constructor lands on a random-access tag.
--
-- A reader seeing that tag takes the bytes after it for a size field.
case_ordinary_tag_into_the_random_access_range_is_refused :: Assertion
case_ordinary_tag_into_the_random_access_range_is_refused =
  tagOf (manyConDDefs (ranTagBase + 1)) ("K" ++ show (ranTagBase :: Int))
    >>= expectRefusal "ordinary tag at the random-access base"

-- | A random-access variant is offset by 'ranTagBase', so it runs out sooner.
--
-- Past 'selectiveIndirectionAlt' the tag is one the collector has reserved,
-- and a traversal takes the node for an indirection.
case_random_access_tag_into_the_reserved_range_is_refused :: Assertion
case_random_access_tag_into_the_reserved_range_is_refused = do
  let n = selectiveIndirectionAlt - ranTagBase
      dds = ranVariantsOf (manyConDDefs (n + 1))
  tagOf dds (toRelRANDataCon ("K" ++ show (n :: Int)))
    >>= expectRefusal "random-access tag at the reserved base"

-- | The one below it still fits, so the boundary is where it is claimed.
case_last_random_access_tag_is_accepted :: Assertion
case_last_random_access_tag_is_accepted = do
  let n = selectiveIndirectionAlt - ranTagBase
      dds = ranVariantsOf (manyConDDefs n)
  r <- tagOf dds (toRelRANDataCon ("K" ++ show (n - 1 :: Int)))
  case r of
    Right t -> t @?= fromIntegral (selectiveIndirectionAlt - 1 :: Int)
    Left e -> assertFailure ("expected the last random-access tag to fit: " ++ show e)

-- | Replace every constructor with its relative random-access variant.
ranVariantsOf :: DDefs (UrTy ()) -> DDefs (UrTy ())
ranVariantsOf = M.map (\dd -> dd { dataCons = map ran (dataCons dd) })
  where ran (dcon, flds) = (toRelRANDataCon dcon, flds)

tagSpaceTests :: TestTree
tagSpaceTests = $(testGroupGenerator)
