module T_deps where

data Tree = Node Int Tree Tree
          | Leaf Int

buildtree_dep :: Int -> (Int, Tree)
buildtree_dep n =
  if n == 0
  then (1, Leaf 1)
  else
    let (i,x) = buildtree_dep (n-1)
        (j,y) = buildtree_dep (n-1)
    in ((i+j), Node (i+j) x y)

buildtree_nodep :: Int -> (Int, Tree)
buildtree_nodep n =
  if n == 0
  then (1, Leaf 1)
  else
    let m = (n+1)
        (i,x) = buildtree_nodep (n-1)
        (j,y) = buildtree_nodep (n-1)
    in ((i+j), Node m x y)


gibbon_main =
  let (i,tr) = buildtree_dep sizeParam
      (j,tr2) = buildtree_nodep sizeParam
      _ = printPacked tr
      _ = printsym (quote "\n")
      _ = printPacked tr2
  in (i,j)
