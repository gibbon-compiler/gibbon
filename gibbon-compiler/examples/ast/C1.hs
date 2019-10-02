-- Benchmark for doing simple optimizations on a CFG.
-- Based on the C1 language from Essentials of Compilation (Fall19)
--
-- Three passes:
--  * optimize jumps
--    if we have a block like
--        block1: goto block2
--    then we replace all jumps to block1 with jumps to block2
--  * simple dead code elimination
--    remove all blocks that are never jumped to
--  * interpreter
--    evaluate the program with an environment for variable assignments
module C1 where

import Helpers
import Prelude hiding ( Maybe(..), appepnd, foldr, lookup )

data List a = Nil | Cons a (List a)
              deriving Show

data Maybe z = Nothing | Just z
               deriving Show

foldr :: (a -> b -> b) -> b -> List a -> b
foldr f acc ls =
  case ls of
    Nil        -> acc
    Cons x rst -> let acc' = (foldr f acc rst)
                  in f x acc'


append :: List a -> List a -> List a
append xs ys = foldr (\ a b -> Cons a b) ys xs

contains :: (a -> a -> Bool) -> a -> List a -> Bool
contains eqp elm lst =
    case lst of
      Nil -> False
      Cons a rst ->
          if eqp a elm
          then True
          else contains eqp elm rst

lookup :: (a -> a -> Bool) -> a -> List (a,b) -> Maybe b
lookup eqp elm lst =
    case lst of
      Nil -> Nothing
      Cons tup rst ->
          let (k,v) = tup
          in if eqp k elm
             then Just v
             else lookup eqp elm rst

strEq :: Sym -> Sym -> Bool
strEq a b = eqsym a b
    
               
-- C1 Lang

data Arg = IntC Int | VarC Sym | TrueC | FalseC
           deriving Show

data Cmp = EqpC | LtpC
           deriving Show         

data Exp = ArgC Arg | ReadC | NegC Arg | PlusC Arg Arg | NotC Arg | CmpC Cmp Arg Arg
           deriving Show

data Stm = AssignC Sym Exp
           deriving Show

data Tal = RetC Exp | SeqC Stm Tal | GotoC Sym | IfC Cmp Arg Arg Sym Sym
           deriving Show

data Prg = ProgramC (List (Sym, Tal))
           deriving Show

data Val = IntV Int | ErrorV
           deriving Show



-- Optimize Jumps

optimizeJumps :: Prg -> Prg
optimizeJumps p =
    case p of
      ProgramC ls -> let ss = collectTrivial ls
                     in ProgramC (replaceJumps ls ss)

collectTrivial :: List (Sym, Tal) -> List (Sym, Sym)
collectTrivial ls =
    case ls of
      Nil -> Nil
      Cons tup b ->
          let (s,t) = tup
          in consIfTrivial s t (collectTrivial b)

consIfTrivial :: Sym -> Tal -> List (Sym, Sym) -> List (Sym, Sym)
consIfTrivial s t b =
    case t of
      RetC e -> b
      SeqC s t -> b
      GotoC str -> Cons (s,str) b
      IfC c a1 a2 s1 s2 -> b

replaceJumps :: List (Sym, Tal) -> List (Sym, Sym) -> List (Sym, Tal)
replaceJumps ts ss =
    case ts of
      Nil -> Nil
      Cons tup b ->
          let (s,t) = tup
          in Cons (s, replaceJumpsInner t ss) (replaceJumps b ss)

replaceJumpsInner :: Tal -> List (Sym, Sym) -> Tal
replaceJumpsInner t ss =
    case t of
      RetC e -> RetC e
      SeqC s t1 -> SeqC s (replaceJumpsInner t1 ss)
      GotoC str -> GotoC (replaceLabel str ss)
      IfC c a1 a2 s1 s2 -> 
          IfC c a1 a2 (replaceLabel s1 ss) (replaceLabel s2 ss)

replaceLabel :: Sym -> List (Sym, Sym) -> Sym
replaceLabel str ss =
    case ss of
      Nil -> str
      Cons tup rst ->
          let (s1,s2) = tup
          in if eqsym s1 str
             then s2
             else replaceLabel str rst


-- Eliminate Dead Code

eliminateDeadcode :: Prg -> Prg
eliminateDeadcode p =
    case p of
      ProgramC ls ->
          let jmps = collectJumps ls
          in ProgramC (removeBlocks ls (Cons (quote "start") jmps))

collectJumps :: List (Sym,Tal) -> List Sym
collectJumps ts =
    case ts of
      Nil -> Nil
      Cons tup rst ->
          let (s,t) = tup
          in append (collectJumpsTal t) (collectJumps rst)

collectJumpsTal :: Tal -> List Sym
collectJumpsTal t =
    case t of
      RetC e -> Nil
      SeqC st t1 -> collectJumpsTal t1
      GotoC str -> Cons str Nil
      IfC c a1 a2 s1 s2 -> Cons s1 (Cons s2 Nil)


removeBlocks :: List (Sym,Tal) -> List Sym -> List (Sym,Tal)
removeBlocks ts ss =
    case ts of
      Nil -> Nil
      Cons tup rst ->
          let (s,t) = tup
          in if contains strEq s ss
             then Cons (s,t) (removeBlocks rst ss)
             else removeBlocks rst ss


-- C1 Interp

interpPrg :: Prg -> Val
interpPrg p =
    case p of
      ProgramC ls -> case lookup strEq (quote "start") ls of
                       Just t -> interpBlock t ls Nil
                       Nothing -> ErrorV

interpBlock :: Tal -> List (Sym,Tal) -> List (Sym,Int) -> Val
interpBlock t ls vs =
    case t of
      RetC e -> interpExp e vs
      SeqC s t1 -> case interpStm s vs of
                     Nothing -> ErrorV
                     Just vs1 -> interpBlock t1 ls vs1
      GotoC str -> case lookup strEq str ls of
                     Just t1 -> interpBlock t1 ls vs
                     Nothing -> ErrorV
      IfC c a1 a2 s1 s2 -> interpIf c a1 a2 s1 s2 ls vs

interpIf :: Cmp -> Arg -> Arg -> Sym -> Sym ->
            List (Sym,Tal) -> List (Sym,Int) -> Val
interpIf c a1 a2 s1 s2 ls vs =
    case interpExp (CmpC c a1 a2) vs of
      ErrorV -> ErrorV
      IntV i -> if i == 0
                then case lookup strEq s2 ls of
                       Just t -> interpBlock t ls vs
                       Nothing -> ErrorV
                else case lookup strEq s1 ls of
                       Just t -> interpBlock t ls vs
                       Nothing -> ErrorV

interpStm :: Stm -> List (Sym,Int) -> Maybe (List (Sym,Int))
interpStm s vs =
    case s of
      AssignC str exp -> case interpExp exp vs of
                           ErrorV -> Nothing
                           IntV i -> Just (Cons (str,i) vs)

interpExp :: Exp -> List (Sym,Int) -> Val
interpExp e vs =
    case e of
      ArgC a -> interpArg a vs
      ReadC -> IntV 42 -- ReadC always returns 42
      NegC a -> case interpArg a vs of
                  IntV i -> IntV (-i)
                  ErrorV -> ErrorV
      PlusC a1 a2 -> case interpArg a1 vs of
                       ErrorV -> ErrorV
                       IntV i1 -> case interpArg a2 vs of
                                    ErrorV -> ErrorV
                                    IntV i2 -> IntV (i1 + i2)

      NotC a -> case interpArg a vs of
                  ErrorV -> ErrorV
                  IntV i -> if i == 0
                            then IntV 1
                            else if i == 1
                                 then IntV 0
                                 else ErrorV
      CmpC c a1 a2 -> case interpArg a1 vs of
                        ErrorV -> ErrorV
                        IntV i1 -> case interpArg a2 vs of
                                     ErrorV -> ErrorV
                                     IntV i2 -> case c of
                                                  EqpC -> if i1 == i2
                                                          then IntV 1
                                                          else IntV 0
                                                  LtpC -> if i1 < i2
                                                          then IntV 1
                                                          else IntV 0

interpArg :: Arg -> List (Sym,Int) -> Val
interpArg a vs =
    case a of
      IntC i -> IntV i
      VarC s -> case lookup strEq s vs of
                  Just v -> IntV v
                  Nothing -> ErrorV
      TrueC -> IntV 1
      FalseC -> IntV 0
          


-- C1 term

ex1 :: Prg
ex1 = ProgramC (Cons (quote "block1", RetC (ArgC (IntC 0)))
                (Cons (quote "block2", GotoC (quote "block1"))
                 (Cons (quote "block3", RetC (ArgC (IntC 42)))
                  (Cons (quote "start", (SeqC (AssignC (quote "y") ReadC)
                                   (IfC EqpC (VarC (quote "y")) (IntC 1) (quote "block2") (quote "block3"))))
                   Nil))))

-- runners

eval :: Prg -> Int
eval p =
    case (interpPrg (eliminateDeadcode (optimizeJumps p))) of
      IntV i -> i
      ErrorV -> (-1)
      
main :: IO ()
main = do print (eval ex1)

gibbon_main = eval ex1
