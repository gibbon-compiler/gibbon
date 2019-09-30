module X where


data BoolJ = TrueJ | FalseJ
data Node = Inner Int Int  Node Node |
            Leaf Int Int Poly |
            ErrorNode

-- list of coefficient
data Poly = PolyInner Int Poly |
            PolyEnd
  deriving( Show)

getStart :: Node -> Int
getStart n = case n of
 Inner s e left right -> s
 Leaf s e poly -> s
 ErrorNode -> -1

getEnd :: Node -> Int
getEnd n = case n of
 Inner s e left right -> e
 Leaf s e poly -> e
 ErrorNode -> -1

getLeft:: Node -> Node
getLeft n =
   case n of
     Inner s e left right -> left
     Leaf a b c -> ErrorNode
     ErrorNode -> ErrorNode


getRight:: Node -> Node
getRight n =
   case n of
     Inner s e left right -> left
     Leaf a b c -> ErrorNode
     ErrorNode -> ErrorNode

addConstNode :: Node -> Int ->  Node
addConstNode tr c = case tr of
   Inner s e left right -> Inner s e  (addConstNode left c) (addConstNode right c)
   Leaf s e poly -> Leaf s e (addConstPoly poly c)
   ErrorNode -> ErrorNode

addConstPoly :: Poly -> Int -> Poly
addConstPoly poly c = case poly of
   PolyInner v rem -> PolyInner (v+c)  rem
   PolyEnd -> PolyEnd

----------------------------------
scaleConstNode :: Node -> Int ->  Node
scaleConstNode tr c = case tr of
   Inner s e left right -> Inner s e  (scaleConstNode left c) (scaleConstNode right c)
   Leaf s e poly -> Leaf s e (scaleConstPoly poly c)
   ErrorNode -> ErrorNode

scaleConstPoly :: Poly -> Int -> Poly
scaleConstPoly poly c = case poly of
   PolyInner v rem -> PolyInner (v*c) (scaleConstPoly rem c)
   PolyEnd -> PolyEnd

---------------------------------------

--return -1000000 if there is error we do not support if !
f :: Int -> Int -> Int
f a b = if( a==b ) then a else -100000000

addTwoFunctions :: Node -> Node -> Node
addTwoFunctions tree1 tree2 =
  case tree1 of
    Inner s1 e1 left1 right1 ->
      addTwoFunctions2 tree2 s1 e1 left1 right1
    Leaf s e poly ->  addTwoFunctions3 tree2 s e poly
    ErrorNode -> ErrorNode

addTwoFunctions2:: Node ->Int->Int-> Node -> Node -> Node
addTwoFunctions2 tree2 s1 e1 left1 right1  =
   case tree2 of
            Inner s2 e2 left2 right2  ->
               let news = f s1 s2 in
               let newe = f e1 e2 in
               Inner news newe (addTwoFunctions left1 left2)
                                 (addTwoFunctions right1 right2)
            Leaf s e poly  -> ErrorNode
            ErrorNode  -> ErrorNode

addTwoFunctions3:: Node ->Int->Int-> Poly -> Node
addTwoFunctions3 tree2 s1 e1 poly1   =
   case tree2 of
            Inner s2 e2 left2 right2  ->
               ErrorNode
            Leaf s2 e2 poly2  ->
                let news = f s1 s2 in
                let newe = f e1 e2 in
                Leaf news newe (addTwoPolys poly1 poly2)
            ErrorNode  -> ErrorNode

addTwoPolys2:: Poly -> Int  -> Poly -> Poly
addTwoPolys2 p2 v1 rem1  =
   case p2 of
            PolyInner v2 rem2->
               PolyInner (v1+v2) (addTwoPolys rem1 rem2)
            PolyEnd  ->
              PolyInner  v1 rem1

addTwoPolys :: Poly -> Poly -> Poly
addTwoPolys p1 p2 = case p1 of
    PolyInner v1 rem1 ->
       addTwoPolys2 p2 v1 rem1
    PolyEnd  -> p2

---------------------------------------
multTwoFunction :: Node -> Node -> Node
multTwoFunction tree1 tree2 =
  case tree1 of
    Inner s1 e1 left1 right1 ->
      multTwoFunction2 tree2 s1 e1 left1 right1
    Leaf s e poly ->  multTwoFunction3 tree2 s e poly
    ErrorNode -> ErrorNode


multTwoFunction2:: Node ->Int->Int-> Node -> Node -> Node
multTwoFunction2 tree2 s1 e1 left1 right1  =
   case tree2 of
            Inner s2 e2 left2 right2  ->
               let news = f s1 s2 in
               let newe = f e1 e2 in
               Inner news newe (multTwoFunction left1 left2)
                                 (multTwoFunction right1 right2)
            Leaf s e poly  -> ErrorNode
            ErrorNode  -> ErrorNode

multTwoFunction3:: Node ->Int->Int-> Poly -> Node
multTwoFunction3 tree2 s1 e1 poly1   =
   case tree2 of
            Inner s2 e2 left2 right2  ->
               ErrorNode
            Leaf s2 e2 poly2  ->
                let news = f s1 s2 in
                let newe = f e1 e2 in
                Leaf news newe (multTwoPolys poly1 poly2  PolyEnd)
            ErrorNode  -> ErrorNode

appendPoly ::  Poly -> Poly -> Poly
appendPoly p1 p2 = case p1 of
   PolyInner v1 rem1 -> PolyInner v1 (appendPoly rem1 p2)
   PolyEnd -> p2

multTwoPolys :: Poly -> Poly -> Poly ->Poly
multTwoPolys p1 p2 init= case p1 of
    PolyInner v1 rem1 ->
       let init' = PolyInner 0 init in
       addTwoPolys (appendPoly init (scaleConstPoly p2 v1))   (multTwoPolys rem1 p2 init')
    PolyEnd  ->
     PolyEnd --return 0 polynomial to be added to the final result



-- f4 = (f3+ f2)*f5
-- ((f1+f2)+1)*f3
gibbon_main =
  let x =  Leaf 1 1 PolyEnd in
  let f1 = Leaf 1 1 PolyEnd in
  let f2 = Leaf 1 1 PolyEnd in
  let f3 = Leaf 1 1 PolyEnd in
  multTwoFunction (scaleConstNode (multTwoFunction (addConstNode (addTwoFunctions f1 f2) 1) f3)100) x

-- gibbon_main =   (multTwoPolys  (PolyInner 1 (PolyInner 1 (PolyInner 1 PolyEnd))) (PolyInner 1 (PolyInner 1 PolyEnd)) PolyEnd)

-- gibbon_main =  appendPoly (PolyInner 0 PolyEnd) (scaleConstPoly  (PolyInner 1 (PolyInner 1 (PolyInner 1 PolyEnd))) 1)

-- gibbon_main =   (scaleConstPoly  (PolyInner 1 (PolyInner 1 (PolyInner 1 PolyEnd))) 1)

-- main = do
--  print $  gibbon_main

-- addTwoFunctions:: Node -> Node -> Node
-- addTwoFunctions tree1 tree2 = case tree1 of
--     Inner s e left right ->
--         Inner s e (addTwoFunctions left (getLeft tree2))
--                      (addTwoFunctions left (getRight tree2))
--     Leaf s e poly ->  Leaf s e poly
--     ErrorNode -> ErrorNode
-- -- assume to functions are defined on the same space with the same partition
-- -- f3 = f1 + f2
-- addTwoFunctions2 :: Node -> Node -> Node
-- addTwoFunctions2 tree2 left1 =
--     case tree2 of
--       Inner s e left2 right2 -> addTwoFunctions left1 left2

-- addTwoFunctions3 :: Node -> Node -> Node
-- addTwoFunctions3 tree2 right1 =
--     case tree2 of
--       Inner s e left2 right2 -> addTwoFunctions right1 right2