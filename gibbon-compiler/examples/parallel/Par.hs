module Par where

data Foo = A Int
         | B Foo Foo
         | C Foo Foo Foo

-- sumFoo :: Foo -> Int
-- sumFoo foo =
--   case foo of
--     A i     -> i
--     B a b   ->
--       let x = sumFoo a
--           y = sumFoo b
--       in x + y
--     C a b c ->
--       let trp = par (sumFoo a) (sumFoo b) (sumFoo c)
--           x = trp !!! 0
--           y = trp !!! 1
--           z = trp !!! 2
--       in x + y + z


-- mkFoo :: Int -> (Foo, Int)
-- mkFoo i =
--   if i <= 0
--   then (A 1, 9)
--   else if i == 1
--        then
--          let x = mkFoo (i-1)
--              y = mkFoo (i-1)
--              s = (x !!! 1) + (y !!! 1)
--          in (B (x !!! 0) (y !!! 0), s)
--        else
--          let x = mkFoo (i-1)
--              y = mkFoo (i-1)
--              z = mkFoo (i-1)
--              s = (x !!! 1) + (y !!! 1) + (z !!! 1)
--          in (C (x !!! 0) (y !!! 0) (z !!! 0), s)

mkFoo :: Int -> Foo
mkFoo i =
  if i <= 0
  then A 1
  else if i == 1
       then B (mkFoo (i-1)) (mkFoo (i-1))
       else C (mkFoo (i-1)) (mkFoo (i-1)) (mkFoo (i-1))


sumFoo2 :: Foo -> Int
sumFoo2 foo =
  case foo of
    A i     -> i
    B a b   ->
      let x = sumFoo2 a
          y = sumFoo2 b
      in x + y
    C a b c ->
      let x = spawn a (sumFoo2 a)
          y = spawn b (sumFoo2 b)
          z = spawn c (sumFoo2 c)
          _ = sync
      in x + y + z

gibbon_main =
  let x = mkFoo 2
  in sumFoo2 x
