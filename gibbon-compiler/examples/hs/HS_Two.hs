module HS_Two where

import Prelude hiding (succ)

data Tree a = Leaf a
            | Node (Tree a) (Tree a)
  deriving Show

mkTree :: Int -> Tree Int
mkTree n = if n == 0
           then Leaf 1
           else Node (mkTree (n-1)) (mkTree (n-1))

foldrTree :: (a -> b -> b) -> b -> Tree a -> b
foldrTree f acc tr =
  case tr of
    Leaf n   -> f n acc
    Node l r -> let acc1 = foldrTree f acc l
                in foldrTree f acc1 r

plus :: Int -> Int -> Int
plus a b = a + b


{-

Bugs uncovered:

(1) 'specFunDefs' shouldn't just recur on monomorphization obligations collected
in main. If we use 'sumTree' instead of 'foldrTree' in main, no obligations
are collected because 'sumTree' has a monomorphic type. This means that
'foldrTree' won't be monomorphized! So we must always process *all* functions.

(2) (1) causes this too. Because 'mkTree' has a monomorphic type, we
    don't process it and therefore don't collect the datatype mono
    obligation (Tree => Tree_Int). So (Tree a) won't be monomorphized.

-}

-- sumTree :: Tree Int -> Int
-- sumTree tr = foldrTree plus 0 tr


gibbon_main = foldrTree plus 0 (mkTree 10)

main :: IO ()
main = print gibbon_main
