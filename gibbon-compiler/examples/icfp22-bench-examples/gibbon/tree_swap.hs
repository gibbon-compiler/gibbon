data Tree = Leaf Int | Node Int Tree Tree

printTree :: Tree -> ()
printTree tree = case tree of
  Leaf v ->
    let _ = printint v
    in  ()
  Node v l r ->
    let _ = printint v
        _ = printsym (quote " -> ")
        _ = printsym (quote "[")
        _ = printTree l
        _ = printsym (quote ", ")
        _ = printTree r
        _ = printsym (quote "]")
    in  ()

printTree' :: Tree -> ()
printTree' tree = 
    let _ = printTree tree 
        _ = printsym (quote "NEWLINE")
    in ()

mkTree :: Int -> Int -> (Tree, Int)
mkTree i n = if n == 0
  then (Leaf i, i + 1)
  else
    let (a, ia) = mkTree (i + 1) (n - 1)
        (b, ib) = mkTree (ia + 1) (n - 1)
    in  (Node i a b, ib + 1)

swapTree :: Tree -> Tree
swapTree tree = case tree of
  Leaf _     -> tree
  Node v a b -> Node v b a

bench_main :: ()
bench_main =
  let n         = sizeParam
      (tree, _) = mkTree 0 n
      tree'     = swapTree tree
    --   _         = printTree' tree
    --   _         = printTree' tree'
  in  ()

gibbon_main = bench_main
