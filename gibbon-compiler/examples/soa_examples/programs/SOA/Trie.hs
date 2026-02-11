data Trie
  = TNode Int  -- character code
          Int  -- frequency
          Int  -- subtree count
          Int  -- flags
          Trie Trie
  | TLeaf Int  -- terminal count
          Int  -- word id
          Int  -- score
          Int  -- metadata
  | TEmpty

{-# ANN type Trie "Factored" #-}

buildTrie :: Int -> Trie
buildTrie d =
  if d == 0
  then TLeaf (d*2) (d*1) (d*3) (d*5)
  else TNode d (d*5) (d*10) (mod d 2)
       (buildTrie (d-1))
       (buildTrie (d-1))

-- Reduction 1: Total frequency
sumFreq :: Trie -> Int
sumFreq t =
  case t of
    TNode _ f _ _ l r ->
      f + sumFreq l + sumFreq r
    TLeaf _ _ _ _ ->
      0
    TEmpty ->
      0

-- Reduction 2: Count terminals
countWords :: Trie -> Int
countWords t =
  case t of
    TLeaf _ _ _ _ ->
      1
    TNode _ _ _ _ l r ->
      countWords l + countWords r
    TEmpty ->
      0

-- Reduction 3: Subtree size
sumSubtrees :: Trie -> Int
sumSubtrees t =
  case t of
    TNode _ _ sc _ l r ->
      sc + sumSubtrees l + sumSubtrees r
    TLeaf _ _ _ _ ->
      0
    TEmpty ->
      0

-- Reduction 4: Count flagged nodes
countTrieFlags :: Trie -> Int -> Int
countTrieFlags t f =
  case t of
    TNode _ _ _ fl l r ->
      let here = if fl == f then 1 else 0
      in here + countTrieFlags l f + countTrieFlags r f
    TLeaf _ _ _ _ ->
      0
    TEmpty ->
      0

-- Map 1: Scale frequencies
scaleFreq :: Trie -> Int -> Trie
scaleFreq t k =
  case t of
    TNode c f sc fl l r -> let scale = f * k
                            in TNode c scale sc fl (scaleFreq l k) (scaleFreq r k)
    TLeaf t i s m -> TLeaf t i s m
    TEmpty -> TEmpty

-- Map 2: Clear flags
clearTrieFlags :: Trie -> Trie
clearTrieFlags t =
  case t of
    TNode c f sc _ l r ->
      TNode c f sc 0
            (clearTrieFlags l)
            (clearTrieFlags r)
    TLeaf t i s m ->
      TLeaf t i s m
    TEmpty ->
      TEmpty



gibbon_main =
   let _ = printsym (quote "Running progrm Trie: ")
       _ = printsym (quote "NEWLINE")
       trie = buildTrie 15
       _ = printsym (quote "Running pass sum frequency: ")
       _ = printsym (quote "NEWLINE")
       totFreq = iterate (sumFreq trie)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass sum count words: ")
       _ = printsym (quote "NEWLINE")
       totWords = iterate (countWords trie)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass sum subtrees: ")
       _ = printsym (quote "NEWLINE")
       subTreeSize = iterate (sumSubtrees trie)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass count trie flags: ")
       _ = printsym (quote "NEWLINE")
       totFlaggedNodes = iterate (countTrieFlags trie 2)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass scale frequency: ")
       _ = printsym (quote "NEWLINE")
       trie' = iterate (scaleFreq trie 10)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass clear trie flags: ")
       _ = printsym (quote "NEWLINE")
       trie'' = iterate (clearTrieFlags trie')
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
   in (totFreq, totWords, subTreeSize, totFlaggedNodes)






