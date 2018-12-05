module Types where

data Foo = Bar Int
         | Baz {-# NOUNPACK #-} A
               {-# NOUNPACK #-} Foo

data A = MkA
data B = MkB
data C = MkC

add1 :: (A -> B) -> C -> C
add1 f c = c

iamavar :: C
iamavar = MkC

main = let x :: Foo
           x = Bar 1
       in 10
