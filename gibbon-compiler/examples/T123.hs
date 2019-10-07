module T123 where

data Foo = MkFoo1 Foo | MkFoo2
  deriving Show

mkfoo :: Int -> Foo
mkfoo n = if n == 0
          then MkFoo2
          else MkFoo1 (mkfoo (n-1))

getDepth :: Foo -> Int
getDepth foo =
  case foo of
    MkFoo2      -> 0
    MkFoo1 foo1 -> 1 + (getDepth foo1)

gibbon_main = let foo = mkfoo 10
              in bench getDepth foo
