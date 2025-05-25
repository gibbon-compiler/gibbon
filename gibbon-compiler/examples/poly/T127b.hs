module T127b where

data Foo a b = MkFoo a b

data Bar a = MkBar (Foo a Int)

data Baz a = MkBaz (Foo Int a)

gibbon_main =
  let foo = MkFoo 10 20
      _ = printPacked foo
      _ = printsym (quote "\n")
      bar = MkBar foo
      _ = printPacked bar
      _ = printsym (quote "\n")
      --baz = MkBaz (MkFoo 12 20)
      baz = MkBaz foo
      baz2 = MkBaz (MkFoo 10 False)
      _ = printPacked baz2
      _ = printsym (quote "\n")
  in 10
