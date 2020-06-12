module NeedsClosure where

ap :: (a -> b) -> a -> b
ap fn arg = fn arg

id :: a -> a
id x = x

ap2 :: (a -> b) -> a -> b
ap2 fn arg = ap (\a -> fn a) arg
-- ap2 fn arg = ap fn arg

gibbon_main =
    let -- m = 10
        -- n = ap (\_ -> m) 10
        o = ap2 id 10
    in o
