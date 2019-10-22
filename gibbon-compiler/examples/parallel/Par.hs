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


{-# ANN sumFoo (gibbon_payload, [0]) #-}
sumFoo :: Foo -> Int
sumFoo foo =
  case foo of
    A i     -> i
    B a b   ->
      let x = sumFoo a
          y = sumFoo b
      in x + y
    C a b c ->
      -- let x = if is_big a
      --         then let p = spawn (sumFoo a)
      --              in p
      --         else sumFoo a
      --     y = if is_big b
      --         then let q = spawn (sumFoo b)
      --              in q
      --         else sumFoo b
      --     z = if is_big c
      --         then let r = spawn (sumFoo c)
      --              in r
      --         else sumFoo c
      --     t = sync
      -- in x + y + z
      if is_big a
      then
        let x = spawn (sumFoo a)
            y = spawn (sumFoo b)
            z = spawn (sumFoo c)
            a = sync
        in x + y + z
      else
        let x = (sumFoo a)
            y = (sumFoo b)
            z = (sumFoo c)
        in x + y + z

        -- let trp = par (sumFoo a) (sumFoo b) (sumFoo c)
        --     x = trp !!! 0
        --     y = trp !!! 1
        --     z = trp !!! 2
        -- in x + y + z
      -- else if is_big a && is_big b
      --      then
      --        let tup = par (sumFoo a) (sumFoo b)
      --            x = tup !!! 0
      --            y = tup !!! 1
      --            z = sumFoo c
      --            in x + y + z
      --      else
      --        let x = sumFoo a
      --            y = sumFoo b
      --            z = sumFoo c
      --        in x + y + z


gibbon_main =
  let x = mkFoo 2
  in sumFoo x
