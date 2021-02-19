module BinTree where

import Gibbon.Prelude
import Fib

data Tree = Leaf Int
          | Node Int Tree Tree

-- build

mkTree_seq :: Int -> Tree
mkTree_seq i =
  if i <= 0
  then Leaf 1
  else
      let x = mkTree_seq (i-1)
          y = mkTree_seq (i-1)
      in Node i x y

mkTree_par :: Int -> Int -> Tree
mkTree_par cutoff i =
  if i <= cutoff
  then (mkTree_seq i)
  else
      let x = spawn (mkTree_par cutoff (i-1))
          y = mkTree_par cutoff (i-1)
          _ = sync
      in Node i x y

-- buildfib

mkTreeFib_seq :: Int -> Tree
mkTreeFib_seq i =
  if i <= 0
  then Leaf (fib_seq 20)
  else
      let x = mkTreeFib_seq (i-1)
          y = mkTreeFib_seq (i-1)
      in Node i x y


mkTreeFib_par :: Int -> Int -> Tree
mkTreeFib_par cutoff i =
  if i <= 0
  then Leaf (fib_seq 20)
  else
      if i <= cutoff
      then mkTreeFib_seq i
      else let x = spawn (mkTreeFib_par cutoff (i-1))
               y = mkTreeFib_par cutoff (i-1)
               _ = sync
           in Node i x y


-- add1

add1Tree_seq :: Tree -> Tree
add1Tree_seq tr =
  case tr of
    Leaf i     -> Leaf (i+1)
    Node i l r ->
      let l1 = (add1Tree_seq l)
          r1 = (add1Tree_seq r)
      in Node i l1 r1

add1Tree_par :: Int -> Tree -> Tree
add1Tree_par cutoff tr =
  case tr of
    Leaf i     -> Leaf (i+1)
    Node i l r ->
      if i <= cutoff
      then add1Tree_seq tr
      else
        let l1 = spawn (add1Tree_par cutoff l)
            r1 = (add1Tree_par cutoff r)
            _  = sync
        in Node i l1 r1

-- sum

sumTree_seq :: Tree -> Int
sumTree_seq foo =
  case foo of
    Leaf i     -> i
    Node i a b ->
      let x = sumTree_seq a
          y = sumTree_seq b
      in x + y

sumTree_par :: Int -> Tree -> Int
sumTree_par cutoff foo =
  case foo of
    Leaf i     -> i
    Node i a b ->
      if i < cutoff
      then sumTree_seq foo
      else
          let x = spawn (sumTree_par cutoff a)
              y = sumTree_par cutoff b
              _ = sync
          in x + y

--------------------------------------------------------------------------------

check_buildfib :: Int -> Tree -> ()
check_buildfib n tr =
    let expected = (2 ^ n) * (fib_seq 20)
        actual = sumTree_seq tr
        _ = print_check (expected == actual)
        _ = printint actual
        _ = printsym (quote "\n")
    in ()

check_buildtree :: Int -> Tree -> ()
check_buildtree n tr =
    let expected = (2 ^ n)
        actual = sumTree_seq tr
        _ = print_check (expected == actual)
        _ = printint actual
        _ = printsym (quote "\n")
    in ()

check_add1tree :: Int -> Tree -> ()
check_add1tree n tr =
    let expected = (2 ^ n) * 2
        actual = sumTree_seq tr
        _ = printint actual
        _ = printsym (quote "\n")
    in ()

check_sumtree :: Int -> Int -> ()
check_sumtree n actual =
    let expected = (2 ^ n)
        _ = print_check (expected == actual)
        _ = printint actual
        _ = printsym (quote "\n")
    in ()


--------------------------------------------------------------------------------

gibbon_main =
    let n = sizeParam
        tr0 = iterate (mkTree_seq n)
        _  = check_buildtree n tr0
        tr1 = iterate (mkTree_par 19 n)
        _  = check_buildtree n tr1
        tr2 = iterate (add1Tree_seq tr0)
        _ = check_add1tree n tr2
        tr3 = iterate (add1Tree_par 19 tr0)
        _ = check_add1tree n tr3
    in ()
