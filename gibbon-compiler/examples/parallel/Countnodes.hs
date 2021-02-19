module Countnodes where

import RacketGrammar

----------------------------------------------------------------------------
-- Countnodes benchmark
----------------------------------------------------------------------------

countNodesSeq :: Toplvl -> Int
countNodesSeq e0 = top e0

countNodesPar :: Toplvl -> Int
countNodesPar e0 = topPar 0 e0

loopToplvlPar :: Int -> ListToplvl -> Int
loopToplvlPar height ls =
    if height >= 9 then (loopToplvl ls) else
    case ls of
        NULLTOPLVL -> nullCost
        CONSTOPLVL tl rst ->
          let ctl = spawn (topPar (height + 1) tl)
              rst = loopToplvlPar height rst
              _ = sync
          in consCost + ctl + rst

topPar :: Int -> Toplvl -> Int
topPar height e =
  case e of
    DefineValues ls e -> tag + (loopSyms ls) + (expr e)
    DefineSyntaxes ls e -> tag + (loopSyms ls) + (expr e)
    BeginTop ls -> tag + (loopToplvlPar height ls)
    Expression e -> tag + (expr e)

--------------------------------------------------------------------------------

loopToplvl :: ListToplvl -> Int
loopToplvl ls =
  case ls of
    CONSTOPLVL tl ls -> consCost + (top tl) + (loopToplvl ls)
    NULLTOPLVL -> nullCost

top :: Toplvl -> Int
top e =
  case e of
    DefineValues ls e -> tag + (loopSyms ls) + (expr e)
    DefineSyntaxes ls e -> tag + (loopSyms ls) + (expr e)
    BeginTop ls -> tag + (loopToplvl ls)
    Expression e -> tag + (expr e)

expr :: Expr -> Int
expr e =
  case e of
    VARREF _s -> tag + scalarCost
    Top _s -> tag + scalarCost
    VariableReference _s -> tag + scalarCost
    VariableReferenceTop _s -> tag + scalarCost
    VariableReferenceNull -> tag
    Quote d -> tag + (datum d)
    QuoteSyntax d -> tag + (datum d)
    QuoteSyntaxLocal d -> tag + (datum d)
    Lambda f lse -> tag + (formals f) + (loopExpr lse)
    CaseLambda cases -> tag + (loopLambdaCase cases)
    LetValues binds body -> tag + (loopLvbind binds) + (loopExpr body)
    LetrecValues binds body -> tag + (loopLvbind binds) + (loopExpr body)
    If e1 e2 e3 -> tag + (expr e1) + (expr e2) + (expr e3)
    Begin exprs -> tag + (loopExpr exprs)
    Begin0 e1 exprs -> tag + (expr e1) + (loopExpr exprs)
    App e1 es -> tag + (expr e1) + (loopExpr es)
    SetBang _s e1 -> tag + scalarCost + (expr e1)
    WithContinuationMark e1 e2 e3 -> tag + (expr e1) + (expr e2) + (expr e3)

loopSyms :: ListSym -> Int
loopSyms ls =
  case ls of
    CONSSYM _s ls -> consCost + scalarCost + (loopSyms ls)
    NULLSYM -> nullCost

formals :: Formals -> Int
formals f =
  case f of
    F1 ls -> tag + (loopSyms ls)
    F2 ls _s -> tag + scalarCost + (loopSyms ls)
    F3 _s -> tag + scalarCost

loopExpr :: ListExpr -> Int
loopExpr ls =
  case ls of
    CONSEXPR e ls -> consCost + (expr e) + (loopExpr ls)
    NULLEXPR -> nullCost

loopLambdaCase :: LAMBDACASE -> Int
loopLambdaCase ls =
  case ls of
    CONSLAMBDACASE f le ls ->
      consCost + (formals f) + (loopExpr le) + (loopLambdaCase ls)
    NULLLAMBDACASE -> nullCost

loopLvbind :: LVBIND -> Int
loopLvbind ls =
  case ls of
    CONSLVBIND syms e ls ->
      consCost + (loopSyms syms) + (expr e) + (loopLvbind ls)
    NULLLVBIND -> nullCost

datum :: Datum -> Int
datum dt =
  case dt of
    INTLIT _i -> tag + scalarCost


--------------------------------------------------------------------------------

nullCost :: Int
nullCost = 1

consCost :: Int
consCost = 1

scalarCost :: Int
scalarCost = 0

tag :: Int
tag = 1
