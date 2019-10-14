-- Benchmark for doing simple optimizations on a CFG.
-- Based on the C1 language from Essentials of Compilation (Fall19)

module C1 where

import Helpers
import Prelude hiding ( List(..), Maybe(..), appepnd, foldr, lookup )

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

containsSym :: Sym -> List Sym -> Bool
containsSym elm lst =
    case lst of
      Nil -> False
      Cons a rst ->
          if eqsym a elm
          then True
          else containsSym elm rst

lookupBlock :: Sym -> Blk -> Maybe Tal
lookupBlock elm lst =
    case lst of
      BlockNil -> Nothing
      BlockCons k v rst ->
          if eqsym k elm
          then Just v
          else lookupBlock elm rst

lookupInt :: Sym -> Env -> Maybe Int
lookupInt elm lst =
    case lst of
      EnvNil -> Nothing
      EnvCons k v rst ->
          if eqsym k elm
          then Just v
          else lookupInt elm rst
               

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

data Prg = ProgramC Blk
           deriving Show

data Val = IntV Int | ErrorV
           deriving Show

data Env = EnvCons Sym Int Env
         | EnvNil

data Blk = BlockCons Sym Tal Blk
         | BlockNil
           deriving Show



-- Optimize Jumps

data Alias = AliasCons Sym Sym Alias
           | AliasNil

optimizeJumps :: Prg -> Prg
optimizeJumps p =
    case p of
      ProgramC ls -> let ss = collectTrivial ls
                     in ProgramC (replaceJumps ls ss)

collectTrivial :: Blk -> Alias
collectTrivial ls =
    case ls of
      BlockNil -> AliasNil
      BlockCons s t b ->
          consIfTrivial s t (collectTrivial b)

consIfTrivial :: Sym -> Tal -> Alias -> Alias
consIfTrivial s t b =
    case t of
      RetC e -> b
      SeqC s t -> b
      GotoC str -> AliasCons s str b
      IfC c a1 a2 s1 s2 -> b

replaceJumps :: Blk -> Alias -> Blk
replaceJumps ts ss =
    case ts of
      BlockNil -> BlockNil
      BlockCons s t b ->
          BlockCons s (replaceJumpsInner t ss) (replaceJumps b ss)

replaceJumpsInner :: Tal -> Alias -> Tal
replaceJumpsInner t ss =
    case t of
      RetC e -> RetC e
      SeqC s t1 -> SeqC s (replaceJumpsInner t1 ss)
      GotoC str -> GotoC (replaceLabel str ss)
      IfC c a1 a2 s1 s2 -> 
          IfC c a1 a2 (replaceLabel s1 ss) (replaceLabel s2 ss)

replaceLabel :: Sym -> Alias -> Sym
replaceLabel str ss =
    case ss of
      AliasNil -> str
      AliasCons s1 s2 rst ->
          if eqsym s1 str
          then s2
          else replaceLabel str rst


-- Eliminate Dead Code

eliminateDeadcode :: Prg -> Prg
eliminateDeadcode p =
    case p of
      ProgramC ls ->
          let jmps = collectJumps ls
          in ProgramC (removeBlocks ls (Cons (quote "start") jmps))

collectJumps :: Blk -> List Sym
collectJumps ts =
    case ts of
      BlockNil -> Nil
      BlockCons s t rst ->
          append (collectJumpsTal t) (collectJumps rst)

collectJumpsTal :: Tal -> List Sym
collectJumpsTal t =
    case t of
      RetC e -> Nil
      SeqC st t1 -> collectJumpsTal t1
      GotoC str -> Cons str Nil
      IfC c a1 a2 s1 s2 -> Cons s1 (Cons s2 Nil)


removeBlocks :: Blk -> List Sym -> Blk
removeBlocks ts ss =
    case ts of
      BlockNil -> BlockNil
      BlockCons s t rst ->
          if containsSym s ss
          then BlockCons s t (removeBlocks rst ss)
          else removeBlocks rst ss


-- C1 Interp

interpPrg :: Prg -> Val
interpPrg p =
    case p of
      ProgramC ls -> case lookupBlock (quote "start") ls of
                       Just t -> interpBlock t ls EnvNil
                       Nothing -> ErrorV

interpBlock :: Tal -> Blk -> Env -> Val
interpBlock t ls vs =
    case t of
      RetC e -> interpExp e vs
      SeqC s t1 -> let vs1 = interpStm s vs
                   in case vs1 of
                        EnvNil -> ErrorV
                        EnvCons _k _v _rst -> interpBlock t1 ls vs1
      GotoC str -> case lookupBlock str ls of
                     Just t1 -> interpBlock t1 ls vs
                     Nothing -> ErrorV
      IfC c a1 a2 s1 s2 -> interpIf c a1 a2 s1 s2 ls vs

interpIf :: Cmp -> Arg -> Arg -> Sym -> Sym ->
            Blk -> Env -> Val
interpIf c a1 a2 s1 s2 ls vs =
    case interpExp (CmpC c a1 a2) vs of
      ErrorV -> ErrorV
      IntV i -> if i == 0
                then case lookupBlock s2 ls of
                       Just t -> interpBlock t ls vs
                       Nothing -> ErrorV
                else case lookupBlock s1 ls of
                       Just t -> interpBlock t ls vs
                       Nothing -> ErrorV

interpStm :: Stm -> Env -> Env -- Maybe (List (Sym,Int))
interpStm s vs =
    case s of
      AssignC str exp -> case interpExp exp vs of
                           ErrorV -> EnvNil
                           IntV i -> EnvCons str i vs

interpExp :: Exp -> Env -> Val
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

interpArg :: Arg -> Env -> Val
interpArg a vs =
    case a of
      IntC i -> IntV i
      VarC s -> case lookupInt s vs of
                  Just v -> IntV v
                  Nothing -> ErrorV
      TrueC -> IntV 1
      FalseC -> IntV 0
          


-- C1 term

ex1 :: Prg
ex1 = ProgramC (BlockCons (quote "block1") (RetC (ArgC (IntC 0)))
                (BlockCons (quote "block2") (GotoC (quote "block1"))
                 (BlockCons (quote "block3") (RetC (ArgC (IntC 42)))
                  (BlockCons (quote "start") ((SeqC (AssignC (quote "y") ReadC)
                                   (IfC EqpC (VarC (quote "y")) (IntC 1) (quote "block2") (quote "block3"))))
                   BlockNil))))

-- runners

eval :: Prg -> Int
eval p =
    case (interpPrg p) of
      IntV i -> i
      ErrorV -> (-1)
      
main :: IO ()
main = do print (eval (optimizeJumps ex1))

gibbon_main = eval (optimizeJumps ex1)
