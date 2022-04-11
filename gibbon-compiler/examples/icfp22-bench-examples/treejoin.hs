-- source: https://github.com/ghc/nofib/blob/f34b90b5a6ce46284693119a06d1133908b11856/gc/treejoin/Main.hs

import           Gibbon.Vector

data Maybe z = Nothing | Just z
               deriving Show

type Key = Int

data Tree e =
    Node Key (Tree e) (Tree e)
    | Leaf Key e
    | Empty
    | ErrorNode

type Entity = (Int, Int, Int)
type Join = (Int, Int, Int, Int, Int)

insertT :: Key -> entity -> Tree entity -> Tree entity
insertT k e t = case t of
  Node k' l r -> if k <= k' then Node k' (insertT k e l) r else Node k' l (insertT k e r)
  Leaf k' v   -> if k < k' then Node k (Leaf k e) (Leaf k' v) else if k > k' then Node k' (Leaf k' v) (Leaf k' e) else ErrorNode
  Empty       -> Leaf k e
  ErrorNode   -> ErrorNode


lookupT :: Key -> Tree entity -> Maybe entity
lookupT k n = case n of
  Node k' l r -> if k <= k' then lookupT k l else lookupT k r

  Leaf k' e   -> if k == k' then Just e else Nothing

  Empty       -> Nothing
  ErrorNode   -> Nothing

mkTree :: (Entity -> Key) -> Vector (Int, Int, Int) -> Tree Entity -> Tree Entity
mkTree fk pts t = if length pts == 0
  then t
  else
    let pt   = head pts
        pts' = tail pts
        k    = fk pt
    in  mkTree fk pts' (insertT k pt t)


join :: Tree Entity -> Tree Entity -> Tree Join -> Tree Join
join t1 t2 j = case t1 of
  ErrorNode -> ErrorNode
  Empty     -> j
  Leaf k v ->
    let (a, b, c) = v
        t2'       = lookupT c t2
        res       = case t2' of
          Nothing -> j
          Just w  -> let (d, e, f) = w in insertT c (a, b, c, d, e) j
    in  case t2 of
          Empty     -> j
          Node _ _  -> res
          Leaf _ _  -> res
          ErrorNode -> ErrorNode
  Node k l r -> case t2 of
    Empty     -> j
    Node _ _  -> join l t2 (join r t2 j)
    Leaf _ _  -> join l t2 (join r t2 j)
    ErrorNode -> ErrorNode

bench_main :: ()
bench_main =
  let f :: Vector Entity
      f1, f2 :: Vector Entity
      len, half :: Int
      f        = readArrayFile Nothing
      len      = length f
      half     = div len 2
      (f1, f2) = splitAt half f
      fk       = (\(x, _, _) -> x)
      t1       = mkTree fk f1 Empty
      t2       = mkTree fk f2 Empty
      _        = join t1 t2 Empty
  in  ()

gibbon_main = bench_main
