-- Written by jazullo.
import Data.Maybe (isJust)

data B = B Bool deriving Show

tru :: B
tru = B True

fal :: B
fal = B False

unB :: B -> Bool
unB bPacked = case bPacked of
  B b -> b

data I = I Int deriving Show
data O = Lt | Eq | Gt deriving Show

unI :: I -> Int
unI iPacked = case iPacked of
  I i -> i

cmp :: I -> I -> O
cmp ip1 ip2 =
  let
    i1 = unI ip1
    i2 = unI ip2
  in if i1 < i2 then Lt
  else if i1 > i2 then Gt
  else Eq

data RBT
  = Empty
  | Node B I RBT RBT
  deriving Show

empty :: RBT
empty = Empty

singleton :: I -> RBT
singleton x = Node tru x Empty Empty

insert :: I -> RBT -> RBT
insert e1 t = case t of
  Empty -> singleton e1
  Node colorx x left right ->
    flipColors (rotateRight (rotateLeft (case cmp x e1 of
      Gt -> Node colorx x left (insert e1 right)
      Lt -> Node colorx x (insert e1 left) right
      Eq -> t
    )))

rotateLeft :: RBT -> RBT
rotateLeft t = case t of
  Empty -> Empty
  Node colorx x leftx rightx -> case rightx of
    Empty -> t
    Node c z leftz rightz ->
      if isRed rightx && isBlack leftx
      then Node colorx z (Node tru x leftx leftz) rightz
      else t

rotateRight :: RBT -> RBT
rotateRight t = case t of
  Empty -> Empty
  Node colorx x leftx rightx -> case leftx of
    Empty -> t
    Node c y lefty righty ->
      if isRed leftx && isRed lefty
      then Node colorx y lefty (Node tru x righty rightx)
      else t

flipColors :: RBT -> RBT
flipColors t = case t of
  Empty -> Empty
  Node c x leftx rightx -> case leftx of
    Empty -> t
    Node c1 y lefty righty -> case rightx of
      Empty -> t
      Node c2 z leftz rightz ->
        if isRed leftx && isRed rightx
        then Node tru x (Node fal y lefty righty) (Node fal z leftz rightz)
        else t

isRed :: RBT -> Bool
isRed t = case t of
  Empty -> False
  Node c1 x l r -> unB c1

isBlack :: RBT -> Bool
isBlack t = case t of
  Empty -> True
  Node c1 x l r -> if unB c1 then False else True

ins :: Int -> RBT -> RBT
ins x t = insert (I x) t

mini :: RBT -> I
mini t = case t of
  Empty -> I (0 - 1)
  Node c x l r -> case l of
    Empty -> x
    Node cl xl ll rl -> mini l

--------------------------------------------------------------------------------

checkBlackHeight :: RBT -> Maybe Int
checkBlackHeight tree =
  case tree of
    Empty -> Just 1
    Node c x l r ->
      let mb_lh = checkBlackHeight l
          mb_rh = checkBlackHeight r in
      case mb_lh of
        Nothing -> Nothing
        Just lh -> case mb_rh of
                     Nothing -> Nothing
                     Just rh -> if not (lh == rh)
                                then Nothing
                                else if isBlack tree
                                then Just (lh + 1)
                                else if (isBlack l) && (isBlack r)
                                then Nothing
                                else Just lh

checkTree :: RBT -> Bool
checkTree root =
{-

-- True if the given list is ordered
isSorted :: Ord a => [a] -> Bool
isSorted = undefined

-- True if every red node only has black children
checkRedParents :: RBTree a -> Bool
checkRedParents = undefined

-}
  -- isSorted (inorder root) &&
  -- checkRedParents root &&
  isJust (checkBlackHeight root) &&
  isBlack root

main =
  let
    t1 = ins 5 empty
    t2 = ins 3 t1
    t3 = ins 8 t2
    t4 = ins 9 t3
    t5 = ins 4 t4
    t6 = ins 1 t5
  in do
    print t6
    print (checkTree t6)
