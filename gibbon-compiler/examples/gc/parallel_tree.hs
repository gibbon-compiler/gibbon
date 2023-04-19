data Tree = Leaf Int
          | Node Int Tree Tree

mkTree_seq :: Int -> Tree
mkTree_seq i =
  if i <= 0
  then
    -- Just to trigger allocations in thread-local nurseries.
    case (Leaf 1) of
      Leaf x -> Leaf x
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

sumTree_seq :: Tree -> Int
sumTree_seq foo =
  case foo of
    Leaf i     -> i
    Node i a b ->
      let x = sumTree_seq a
          y = sumTree_seq b
      in x + y

gibbon_main =
  let tr = mkTree_par 10 sizeParam
  in sumTree_seq tr
