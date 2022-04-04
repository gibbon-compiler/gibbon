module TuplesInDatacon where

data Foo a = MkFoo a

mkFoo :: (Int,Int) -> Foo (Int,Int)
mkFoo x = MkFoo x

getx :: Foo (Int,Int) -> Int
getx foo = case foo of
             MkFoo tup -> fst tup

gety :: Foo (Int,Int) -> Int
gety foo = case foo of
             MkFoo tup -> snd tup

gibbon_main =
  let foo = mkFoo (10,20)
      x = getx foo
      y = gety foo
  in (x,y)
