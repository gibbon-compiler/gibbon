module Bench where

import Basics
import Gibbon.Vector 
import Gibbon.PList

type String = Vector Char

data PackedBool = B Int

data DecisionTree = Node PackedBool DecisionTree DecisionTree Inline | Leaf Inline



mkRandomDecisionTree :: Int -> DecisionTree
mkRandomDecisionTree depth = if depth <= 0 then Leaf (Str (getRandomString 10))
                             else 
                                let randBool = mod rand 2 
                                    randString = getRandomString 10 
                                    inline = Str randString
                                    leftSubtree = mkRandomDecisionTree (depth-1) 
                                    rightSubtree = mkRandomDecisionTree (depth-1)
                                  in Node (B randBool) leftSubtree rightSubtree inline



fromInline :: Inline -> String 
fromInline inline = case inline of 
                            Str a -> a

fromBool :: PackedBool -> Int 
fromBool b = case b of 
                B bb -> bb

merge_plist :: PList Inline -> PList Inline -> PList Inline 
merge_plist lst1 lst2 = case lst1 of 
                            Cons x rst -> Cons x (merge_plist rst lst2)
                            Nil -> lst2 


append_plist :: PList Inline -> Inline -> PList Inline 
append_plist lst elem = case lst of 
                              Nil -> (Cons elem) Nil 
                              Cons x rst -> Cons x (append_plist rst elem)

singleton_plist :: Inline -> PList Inline 
singleton_plist elem = (Cons elem) Nil


accumulateDecisions :: DecisionTree -> PList Inline
accumulateDecisions tree = case tree of 
                                Node b left right str -> let bb = fromBool b 
                                                           in if bb == 1
                                                              then 
                                                                let curr = append_plist Nil str
                                                                    vecLeft = accumulateDecisions left 
                                                                    cc = singleton_plist (Str (getRandomString 10))
                                                                    vecRight = accumulateDecisions right 
                                                                 in merge_plist (merge_plist curr vecLeft) vecRight
                                                              else 
                                                                let vecLeft = accumulateDecisions left 
                                                                    vecRight = accumulateDecisions right
                                                                  in merge_plist vecLeft vecRight
                                                                       
                                Leaf str -> (Cons str) Nil


gibbon_main = 
    let tree = mkRandomDecisionTree 2
        vec  = accumulateDecisions tree 
     in printPacked vec

--- filter 

--- Map 

--- Search 

--- Length 
