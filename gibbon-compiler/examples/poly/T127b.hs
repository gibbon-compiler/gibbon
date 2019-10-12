module T127b where

data Foo a b = MkFoo a b

data Bar a = MkBar (Foo a Int)

data Baz a = MkBaz (Foo Int a)

gibbon_main =
  let foo = MkFoo 10 20
      bar = MkBar foo
      baz = MkBaz foo
      baz2 = MkBaz (MkFoo 10 False)
  in 10
