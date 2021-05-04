{-# LANGUAGE LinearTypes      #-}
{-# LANGUAGE TypeApplications #-}

module TestParse where

import Gibbon.Prim

id :: a %1-> a
id x = x

data Foo = MkFoo

gibbon_main =
    let
        pts0 :: Vector (Float, Float, Float)
        pts0 = readArrayFile Nothing

        pts1 :: Vector (Float, Float, Float)
        pts1 = readArrayFile (Nothing)

        pts2 :: Vector (Float, Float)
        pts2 = readArrayFile (Just ("/dir/abc.txt", 10))

        pakd1 :: Foo
        pakd1 = readPackedFile @Foo Nothing

        pakd2 :: Foo
        pakd2 = readPackedFile @Foo (Just "/dir/tree.gpkd")
    in ()
