-- Test specialization

-- Not supported yet :(
-- import Prelude

module Spec1 where

foo :: a -> b -> a -> a
foo x y z = x

bar :: a -> b -> a
bar x y = foo x y x

baz :: Int -> Int -> Int
baz x y = x + y

main =
    let
        v1 :: Int
        v1 = bar 10 False

        id2 :: a -> a
        id2 x = x

    in (v1 + id2 10 + baz 10 20, id2 True)
