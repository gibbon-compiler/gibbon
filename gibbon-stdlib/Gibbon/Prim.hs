{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LinearTypes         #-}

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
    , printsym, printint, printfloat, printbool, printPacked

      -- * Command-line arguments
    , sizeParam, readArrayFile, readPackedFile, writePackedFile

      -- * Benchmarking
    , bench, timeit, iterate

      -- * Vectors
    , Vector, valloc, vlength, vnth, vmerge, vslice, vconcat, vsort, vfree, vfree2
    , inplacevupdate, inplacevsort

      -- * Linked lists
    , List, is_empty_ll, alloc_ll, cons_ll, head_ll, tail_ll
    , free_ll, free2_ll, copy_ll

      -- * Sets and Maps of symbols
    , SymSet, empty_set, insert_set, contains_set
    , SymHash, empty_hash, insert_hash, lookup_hash, contains_hash
    , IntHash, insert_int_hash, lookup_int_hash, contains_int_hash

      -- * Parallelism
    , spawn, sync, lsync, par, getNumProcessors, is_big

      -- * Tuples
    , fst, snd

      -- * Error reporting
    , error

      -- * Linear types
    , Ur(..), (&), lseq, unsafeToLinear, unsafeAlias
     
      --maybe 
    , Maybe(..), isJust, isNothing, fromJust, fromMaybe

    ) where

import Prelude hiding (tan, iterate, sqrt)

--------------------------------------------------------------------------------
-- Packed (serialized) values
--------------------------------------------------------------------------------

class Packed a where

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

printPacked :: Packed a => a -> ()
printPacked = undefined

copyPacked :: Packed a => a -> a
copyPacked = undefined

travPacked :: Packed a => a -> ()
travPacked = undefined

--------------------------------------------------------------------------------
-- Command-line arguments
--------------------------------------------------------------------------------

sizeParam :: Int
sizeParam = undefined

readArrayFile :: Maybe (String, Int) -> Vector a
readArrayFile = undefined

readPackedFile :: Packed a => Maybe String -> a
readPackedFile = undefined

writePackedFile :: Packed a => String -> a -> ()
writePackedFile = undefined

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

vlength :: Vector a %1-> Int
vlength = undefined

vnth :: Vector a %1-> Int -> a
vnth = undefined

vslice ::   Int -- Starting index
       ->   Int -- length
       ->   Vector a
       %1-> Vector a
vslice = undefined

vmerge :: Vector a %1-> Vector a %1-> Vector a
vmerge = undefined

vconcat :: Vector (Vector a) -> Vector a
vconcat = undefined

vsort :: Vector a %1-> (a -> a -> Int) -> Vector a
vsort = undefined

vfree, vfree2 :: Vector a %1-> ()
vfree  = undefined
vfree2 = undefined

inplacevupdate :: Vector a %1-> Int -> a -> Vector a
inplacevupdate = undefined

inplacevsort :: Vector a %1-> (a -> a -> Int) -> Vector a
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

spawn :: a %1-> a
spawn = undefined

sync :: ()
sync = undefined

lsync :: Ur ()
lsync = undefined

par :: [a] -> [a]
par = undefined

getNumProcessors :: Int
getNumProcessors = undefined

is_big :: a -> Bool
is_big = undefined

--------------------------------------------------------------------------------
-- Linear types (taken from linear-base)
--------------------------------------------------------------------------------

{-| https://hackage.haskell.org/package/linear-base-0.1.0/docs/Data-Unrestricted-Internal-Ur.html#t:Ur

    The type and the data constructor are both erased by the parser.
-}
data Ur a where
    Ur :: a -> Ur a


{-| https://hackage.haskell.org/package/linear-base-0.1.0/docs/Prelude-Linear.html#v:-38-

    This is parsed as a let-binding:

        exp & (\x -> bod) ====> let x = exp in bod
-}
(&) :: a %1 -> (a %1 -> b) %1 -> b
(&) = undefined

{-| https://hackage.haskell.org/package/linear-base-0.1.0/docs/Prelude-Linear.html#v:lseq

    This is parsed as follows:

        a `lseq` b ====> b
-}
lseq :: a %1-> b %1-> b
lseq = undefined

{-| This is directly desugared as a tuple (by the parser itself), and the L0 specializer
    erases this tuple construction and projections out of it.

        unsafeAlias a & (\x -> bod)
    ====>
        (a,a) & (\x -> bod)
    ====>
        let x = (a,a) in bod
    ====>
        subst (fst x) a (subst (snd x) a bod)
-}
unsafeAlias :: a %1-> (a,a)
unsafeAlias = undefined

{-| https://hackage.haskell.org/package/linear-base-0.1.0/docs/Unsafe-Linear.html#v:toLinear

    This is parsed as follows:

        unsafeToLinear x ====> x

-}
unsafeToLinear :: (a %p-> b) %1-> (a %1-> b)
unsafeToLinear = undefined

------ Maybe functions -------

isJust :: Maybe a -> Bool 
isJust val = case val of 
		Nothing -> False 
		Just a  -> True


isNothing :: Maybe a -> Bool 
isNothing val = case val of 
		  Nothing -> True 
		  Just a  -> False 


fromJust :: Maybe Int -> Int 
fromJust val = case val of 
		Nothing -> (error "Maybe fromJust Nothing" :: Int) 
  		Just x  -> x

fromMaybe :: a -> Maybe a -> a 
fromMaybe d x = case x of 
		   Nothing -> d 
		   Just v  -> v