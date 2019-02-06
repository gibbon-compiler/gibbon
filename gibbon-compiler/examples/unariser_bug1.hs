module UnariserBug1 where

data Foo = FooK
  deriving Show

foo :: Int -> (Foo, (Foo, Int))
foo i = (FooK, (FooK, 10))

gibbon_main = foo 10

main :: IO ()
main = print gibbon_main
