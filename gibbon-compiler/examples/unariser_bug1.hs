module UnariserBug1 where

data Foo = FooK
  deriving Show

foo :: Int -> (Foo, (Foo, Int))
foo i = (FooK, (FooK, i))

gibbon_main =
  let x = foo 10
  in x

main :: IO ()
main = print gibbon_main
