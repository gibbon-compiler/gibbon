{-# OPTIONS_GHC -Wno-typed-holes #-}

module Gibbon.Prim
    (
      -- * Primitive types
      Int, Float, Bool(..), Sym

      -- * Primitive operations
    , (==), (+), (-), (*), quot, (<), (>), (<=), (>=), (^), div, mod
    , (.<.), (.>.)
    , (||), (&&)
    , quote, printsym
    , fst, snd

      -- * Vectors
    , Vector, valloc, vlength, vnth, vslice, inplacevupdate
    , vsort, inplacevsort

      -- * Parallelism
    , spawn, sync, par, getNumProcessors

      -- * TODO: others
    ) where

import Prelude

--------------------------------------------------------------------------------
-- Primitives
--------------------------------------------------------------------------------

data Sym

quote :: String -> Sym
quote = _builtin

printsym :: Sym -> Sym
printsym = _builtin

--------------------------------------------------------------------------------
-- Floating point numbers
--------------------------------------------------------------------------------

(.<.) :: Float -> Float -> Bool
(.<.) = (<)

(.>.) :: Float -> Float -> Bool
(.>.) = (>)

--------------------------------------------------------------------------------
-- Vectors
--------------------------------------------------------------------------------

data Vector a

valloc :: Int -> Vector a
valloc = _builtin

vlength :: Vector a -> Int
vlength = _builtin

vnth :: Vector a -> Int -> a
vnth = _builtin

vslice :: Int -- Starting index
       -> Int -- length
       -> Vector a
       -> Vector a
vslice = _builtin

inplacevupdate :: Vector a -> Int -> a -> Vector a
inplacevupdate = _builtin

vsort :: Vector a -> (a -> a -> Int) -> Vector a
vsort = _builtin

inplacevsort :: Vector a -> (a -> a -> Int) -> Vector a
inplacevsort = _builtin

--------------------------------------------------------------------------------
-- Parallelism
--------------------------------------------------------------------------------

spawn :: a -> a
spawn = _builtin

sync :: ()
sync = _builtin

par :: [a] -> [a]
par = _builtin

getNumProcessors :: Int
getNumProcessors = _builtin
