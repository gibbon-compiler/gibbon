module TestStrings where

data Foo = MkFoo (Vector Char)

headFoo :: Foo -> Char
headFoo foo =
  case foo of
    MkFoo str -> vnth str 0

gibbon_main =
  let
    str :: Vector Char
    str = "hello"
    foo = MkFoo str
    x = headFoo foo
    y = 'i'
  in (x, y)
