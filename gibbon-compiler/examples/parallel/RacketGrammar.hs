module Grammar where

data ListToplvl = CONSTOPLVL Toplvl ListToplvl
                | NULLTOPLVL


data Toplvl = DefineValues ListSym Expr
            | DefineSyntaxes ListSym Expr
            | BeginTop ListToplvl
            | Expression Expr


data Expr = VARREF Sym
          | Lambda Formals ListExpr
          | CaseLambda LAMBDACASE
          | If Expr Expr Expr
          | Begin ListExpr
          | Begin0 Expr ListExpr
          | LetValues LVBIND ListExpr
          | LetrecValues LVBIND ListExpr
          | SetBang Sym Expr
          | Quote Datum
          | QuoteSyntax Datum
          | QuoteSyntaxLocal Datum
          | WithContinuationMark Expr Expr Expr
          | App Expr ListExpr
          | Top Sym
          | VariableReference Sym
          | VariableReferenceTop Sym
          | VariableReferenceNull


data LVBIND = CONSLVBIND ListSym Expr LVBIND
            | NULLLVBIND


data LAMBDACASE = CONSLAMBDACASE Formals ListExpr LAMBDACASE
                | NULLLAMBDACASE


data Datum = INTLIT Int


data Formals = F1 ListSym
             | F2 ListSym Sym
             | F3 Sym


data ListExpr = CONSEXPR Expr ListExpr
              | NULLEXPR


data ListSym = CONSSYM Sym ListSym
             | NULLSYM
