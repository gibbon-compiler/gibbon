module Gibbon.Prim
    (
      -- * Numerals
      Int, Float
    , (==), (<), (>), (<=), (>=), (+), (-), (*), (^), quot, div, mod
    , (.==.), (.<.), (.>.), (.<=.), (.>=.), (.+.), (.-.), (.*.), (./.)
    , tan, sqrt, rand, frand
    , intToFloat, floatToInt

      -- * Booleans
    , Bool(..) , (||), (&&)

      -- * Symbols
    , Sym, quote, eqsym, gensym

      -- * Printing
    , printsym, printint, printfloat, printbool

      -- * Command-line arguments
    , sizeParam, benchProgParam, readArrayFile, readPackedFile

      -- * Benchmarking
    , bench, timeit, iterate

      -- * Vectors
    , Vector, valloc, vlength, vnth, vslice, vconcat, vsort, vfree, vfree2
    , inplacevupdate, inplacevsort

      -- * Linked lists
    , List, is_empty_ll, alloc_ll, cons_ll, head_ll, tail_ll
    , free_ll, free2_ll, copy_ll

      -- * Sets and Maps of symbols
    , SymSet, empty_set, insert_set, contains_set
    , SymHash, empty_hash, insert_hash, lookup_hash, contains_hash
    , IntHash, insert_int_hash, lookup_int_hash, contains_int_hash

      -- * Parallelism
    , spawn, sync, par, getNumProcessors, is_big

      -- * Tuples
    , fst, snd

      -- * Error reporting
    , error

    ) where

import Prelude hiding ( tan, iterate, sqrt )

--------------------------------------------------------------------------------
-- Floating point numbers
--------------------------------------------------------------------------------

(.==.), (.<.), (.>.), (.<=.), (.>=.) :: Float -> Float -> Bool
(.==.) = undefined
(.<.)  = undefined
(.>.)  = undefined
(.<=.) = undefined
(.>=.) = undefined

(.+.), (.-.), (.*.), (./.) :: Float -> Float -> Float
(.+.) = undefined
(.-.) = undefined
(.*.) = undefined
(./.) = undefined

tan, sqrt :: Float -> Float
sqrt = undefined
tan = undefined

frand :: Float
frand = undefined

rand :: Int
rand = undefined

intToFloat :: Int -> Float
intToFloat = undefined

floatToInt :: Float -> Int
floatToInt = undefined

--------------------------------------------------------------------------------
-- Symbols
--------------------------------------------------------------------------------

data Sym

quote :: String -> Sym
quote = undefined

eqsym :: Sym -> Sym -> Bool
eqsym = undefined

gensym :: Sym
gensym = undefined

--------------------------------------------------------------------------------
-- Printing
--------------------------------------------------------------------------------

printsym :: Sym -> ()
printsym = undefined

printint :: Int -> ()
printint = undefined

printfloat :: Float -> ()
printfloat = undefined

printbool :: Bool -> ()
printbool = undefined

--------------------------------------------------------------------------------
-- Command-line arguments
--------------------------------------------------------------------------------

sizeParam :: Int
sizeParam = undefined

benchProgParam :: Sym
benchProgParam = undefined

{-
 - TODO: Both of these also have a variant with weird type application syntax.
 - Make it more like Haskell.
 -}

readArrayFile :: Maybe (String, Int) -> Vector a
readArrayFile = undefined

readPackedFile :: Maybe String -> a
readPackedFile = undefined

--------------------------------------------------------------------------------
-- Benchmarking
--------------------------------------------------------------------------------

bench :: (a -> b) -> a -> b
bench = undefined

timeit, iterate :: a -> a
timeit = undefined
iterate = undefined

--------------------------------------------------------------------------------
-- Vectors
--------------------------------------------------------------------------------

data Vector a

valloc :: Int -> Vector a
valloc = undefined

vlength :: Vector a -> Int
vlength = undefined

vnth :: Vector a -> Int -> a
vnth = undefined

vslice :: Int -- Starting index
       -> Int -- length
       -> Vector a
       -> Vector a
vslice = undefined

vconcat :: Vector (Vector a) -> Vector a
vconcat = undefined

vsort :: Vector a -> (a -> a -> Int) -> Vector a
vsort = undefined

vfree, vfree2 :: Vector a -> ()
vfree  = undefined
vfree2 = undefined

inplacevupdate :: Vector a -> Int -> a -> Vector a
inplacevupdate = undefined

inplacevsort :: Vector a -> (a -> a -> Int) -> Vector a
inplacevsort = undefined

--------------------------------------------------------------------------------
-- Linked lists
--------------------------------------------------------------------------------

data List a

is_empty_ll :: List a -> Bool
is_empty_ll = undefined

alloc_ll :: List a
alloc_ll = undefined

cons_ll :: a -> List a -> List a
cons_ll = undefined

head_ll :: List a -> a
head_ll = undefined

tail_ll :: List a -> List a
tail_ll = undefined

free_ll, free2_ll :: List a -> ()
free_ll  = undefined
free2_ll = undefined

copy_ll :: List a -> List a
copy_ll = undefined

--------------------------------------------------------------------------------
-- Sets and Maps of symbols
--------------------------------------------------------------------------------

data SymSet

empty_set :: SymSet
empty_set = undefined

insert_set :: SymSet -> Sym -> SymSet
insert_set = undefined

contains_set :: SymSet -> Sym -> Bool
contains_set = undefined

data SymHash

empty_hash :: SymHash
empty_hash = undefined

insert_hash :: SymHash -> Sym -> Sym -> SymHash
insert_hash = undefined

lookup_hash :: SymHash -> Sym -> Sym
lookup_hash = undefined

contains_hash :: SymHash -> Sym -> Bool
contains_hash = undefined

data IntHash

insert_int_hash :: IntHash -> Sym -> Int -> IntHash
insert_int_hash = undefined

lookup_int_hash :: IntHash -> Sym -> Int
lookup_int_hash = undefined

contains_int_hash :: IntHash -> Sym -> Bool
contains_int_hash = undefined

--------------------------------------------------------------------------------
-- Parallelism
--------------------------------------------------------------------------------

spawn :: a -> a
spawn = undefined

sync :: ()
sync = undefined

par :: [a] -> [a]
par = undefined

getNumProcessors :: Int
getNumProcessors = undefined

is_big :: a -> Bool
is_big = undefined
