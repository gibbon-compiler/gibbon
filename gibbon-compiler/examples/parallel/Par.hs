module Par where

data Foo = A Int
         | B Foo Foo
         | C Foo Foo Foo

mkFoo :: Int -> Foo
mkFoo i =
  if i <= 0
  then A 1
  else if i == 1
       then B (mkFoo (i-1)) (mkFoo (i-1))
       else C (mkFoo (i-1)) (mkFoo (i-1)) (mkFoo (i-1))


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

sumFoo2 :: Foo -> Int
sumFoo2 foo =
  case foo of
    A i     -> i
    B a b   ->
      let x = sumFoo2 a
          y = sumFoo2 b
      in x + y
    C a b c ->
      let x = spawn (sumFoo2 a)
          y = spawn (sumFoo2 b)
          z = spawn (sumFoo2 c)
          _ = sync
      in x + y + z

gibbon_main =
  let x = mkFoo 2
  in sumFoo2 x
