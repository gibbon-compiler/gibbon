module T127a where

data Foo a = MkFoo a

data Bar a = MkBar (Foo a)

gibbon_main =
  let foo = MkFoo 10
      bar = MkBar foo
  in 10
