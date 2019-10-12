module T127 where

data Foo a = MkFoo a

data Bar = MkBar (Foo Int)

gibbon_main =
  let foo = MkFoo 10
      bar = MkBar foo
  in 10
