-- @BENCH adt_fields=10
data Trie
  = TNode Int  -- character code
          Int  -- prefix frequency
          Int  -- subtree hint count
          Int  -- node flags
          Trie Trie
  | TLeaf Int  -- terminal count
          Int  -- word id
          Int  -- leaf score
          Int  -- leaf metadata
  | TEmpty

{-# ANN type Trie "Factored" #-}

absI :: Int -> Int
absI x = if x < 0 then 0 - x else x

mixSeed :: Int -> Int -> Int
mixSeed s salt = s * 1103 + salt * 97 + 13

-- Build a synthetic trie with node/leaf statistics used by realistic query passes.
{-# ANN buildTrie "OPT:StoreScalarCounts" #-}
buildTrie :: Int -> Int -> Trie
buildTrie d seed =
  if d == 0
  then
    let term = 1 + mod (absI (mixSeed seed 2)) 3
        wid  = mod (absI (mixSeed seed 3)) 100000
        scr  = 5 + mod (absI (mixSeed seed 5)) 95
        meta = mod (absI (mixSeed seed 7)) 16
    in TLeaf term wid scr meta
  else
    let c  = mod (absI (mixSeed seed 11)) 26
        pf = 1 + mod (absI (mixSeed seed 13)) 120
        sc = 2 * (1 + mod (absI (mixSeed seed 17)) 80)
        fl = mod (absI (mixSeed seed 19)) 4
        l  = buildTrie (d - 1) (mixSeed seed 23)
        r  = buildTrie (d - 1) (mixSeed seed 29)
    in TNode c pf sc fl l r

-- Fold 1: sum node prefix frequencies (dictionary traffic proxy).
sumPrefixFreq :: Trie -> Int
sumPrefixFreq t =
  case t of
    TNode _ f _ _ l r ->
      f + sumPrefixFreq l + sumPrefixFreq r
    TLeaf _ _ _ _ ->
      0
    TEmpty ->
      0

-- Fold 2: count total terminal markers across leaves.
countTerminals :: Trie -> Int
countTerminals t =
  case t of
    TLeaf term _ _ _ ->
      term
    TNode _ _ _ _ l r ->
      countTerminals l + countTerminals r
    TEmpty ->
      0

-- Fold 3: aggregate subtree hint counters from internal nodes.
sumSubtreeHints :: Trie -> Int
sumSubtreeHints t =
  case t of
    TNode _ _ sc _ l r ->
      sc + sumSubtreeHints l + sumSubtreeHints r
    TLeaf _ _ _ _ ->
      0
    TEmpty ->
      0

-- Fold 4: autocomplete candidate quality under a score threshold.
autocompleteTopKProxy :: Trie -> Int -> Int
autocompleteTopKProxy t minScore =
  case t of
    TLeaf term _ score _ ->
      if score >= minScore then term * score else 0
    TNode _ freq _ _ l r ->
      freq + autocompleteTopKProxy l minScore + autocompleteTopKProxy r minScore
    TEmpty ->
      0

-- Fold 5: count nodes/leaves considered cold by runtime metadata/flags.
countLazyNodes :: Trie -> Int -> Int
countLazyNodes t metaCut =
  case t of
    TNode _ _ _ fl l r ->
      let here = if fl == 0 then 1 else 0
      in here + countLazyNodes l metaCut + countLazyNodes r metaCut
    TLeaf _ _ _ meta ->
      if meta < metaCut then 1 else 0
    TEmpty ->
      0

-- Map 1: decay prefix frequencies and leaf scores to emulate time-window refresh.
{-# ANN decayTrieStats "OPT:CanVectorize" #-}
decayTrieStats :: Trie -> Int -> Trie
decayTrieStats t k =
  case t of
    TNode c f sc fl l r ->
      let f2 = (f * k) / 10
          sc2 = (sc * (k + 1)) / 10
      in TNode c f2 sc2 fl
            (decayTrieStats l k)
            (decayTrieStats r k)
    TLeaf term wid score meta ->
      let s2 = (score * k) / 10
      in TLeaf term wid s2 meta
    TEmpty ->
      TEmpty

-- Map 2: clear traversal flags and transient leaf metadata for next query batch.
{-# ANN resetTraversalState "OPT:CanVectorize" #-}
resetTraversalState :: Trie -> Trie
resetTraversalState t =
  case t of
    TNode c f sc _ l r ->
      TNode c f sc 0
            (resetTraversalState l)
            (resetTraversalState r)
    TLeaf term wid score _ ->
      TLeaf term wid score 0
    TEmpty ->
      TEmpty

gibbon_main =
   let _ = printsym (quote "Running program Trie: ")
       _ = printsym (quote "NEWLINE")
       trie = buildTrie (sizeParam + 22) 17

       _ = printsym (quote "Running pass sumPrefixFreq (fold, uses=3): ")
       _ = printsym (quote "NEWLINE")
       totFreq = iterate (sumPrefixFreq trie)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass countTerminals (fold, uses=3): ")
       _ = printsym (quote "NEWLINE")
       totTerms = iterate (countTerminals trie)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass sumSubtreeHints (fold, uses=3): ")
       _ = printsym (quote "NEWLINE")
       hintSum = iterate (sumSubtreeHints trie)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass autocompleteTopKProxy (fold, uses=5): ")
       _ = printsym (quote "NEWLINE")
       topK = iterate (autocompleteTopKProxy trie 40)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass countLazyNodes (fold, uses=4): ")
       _ = printsym (quote "NEWLINE")
       lazyN = iterate (countLazyNodes trie 4)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass decayTrieStats (map, uses=10): ")
       _ = printsym (quote "NEWLINE")
       trie' = iterate (decayTrieStats trie 9)
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       _ = printsym (quote "Running pass resetTraversalState (map, uses=10): ")
       _ = printsym (quote "NEWLINE")
       trie'' = iterate (resetTraversalState trie')
       _ = printsym (quote "End")
       _ = printsym (quote "NEWLINE")
       decayedFreq = sumPrefixFreq trie'
       resetFreq = sumPrefixFreq trie''
   in (totFreq, totTerms, hintSum, topK, lazyN, decayedFreq, resetFreq)
