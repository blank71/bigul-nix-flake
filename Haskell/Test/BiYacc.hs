import GHC.Generics
import Generics.BiGUL hiding (Expr, Pat)
import Generics.BiGUL.AST hiding (Expr, Pat)
import Generics.BiGUL.TH
import Language.Haskell.TH
import BiYaccDef

ruleExprArith0 :: BiGUL (Either ErrorInfo) Expr Arith
ruleExprArith0 =
  $(rule [p| Add _ _ |]
         [p| EAdd _ _ |]
         (update [p| EAdd l r |]
                 [d| l = ruleExprArith0
                     r = ruleTermArith0 |])
         [| ruleExprArith1 |])

ruleExprArith1 :: BiGUL (Either ErrorInfo) Expr Arith
ruleExprArith1 =
  $(rule [p| Sub _ _ |]
         [p| ESub _ _ |]
         (update [p| ESub l r |]
                 [d| l = ruleExprArith0
                     r = ruleTermArith0 |])
         [| ruleExprArith2 |])

ruleExprArith2 :: BiGUL (Either ErrorInfo) Expr Arith
ruleExprArith2 =
  $(rule [p| _ |]
         [p| ETerm _ |]
         (update [p| ETerm t |]
                 [d| t = ruleTermArith0 |])
         [| adaptExprArith |])

adaptExprArith :: BiGUL (Either ErrorInfo) Expr Arith
adaptExprArith =
  CaseV [ $(adaptation [p| Add _ _ |]
                       [p| EAdd _ _ |]
                       (update [p| EAdd l r |]
                               [d| l = ruleExprArith0
                                   r = ruleTermArith0 |])
                       [| EAdd ENull TNull |]),
          $(adaptation [p| Sub _ _ |]
                       [p| ESub _ _ |]
                       (update [p| ESub l r |]
                               [d| l = ruleExprArith0
                                   r = ruleTermArith0 |])
                       [| ESub ENull TNull |]),
          $(adaptation [p| _ |]
                       [p| ETerm _ |]
                       (update [p| ETerm t |]
                               [d| t = ruleTermArith0 |])
                       [| ETerm TNull |])
        ]

ruleTermArith0 :: BiGUL (Either ErrorInfo) Term Arith
ruleTermArith0 =
  $(rule [p| Mul _ _ |]
         [p| TMul _ _ |]
         (update [p| TMul l r |]
                 [d| l = ruleTermArith0
                     r = ruleFactorArith0 |])
         [| ruleTermArith1 |])

ruleTermArith1 :: BiGUL (Either ErrorInfo) Term Arith
ruleTermArith1 =
  $(rule [p| Div _ _ |]
         [p| TDiv _ _ |]
         (update [p| TDiv l r |]
                 [d| l = ruleTermArith0
                     r = ruleFactorArith0 |])
         [| ruleTermArith2 |])

ruleTermArith2 :: BiGUL (Either ErrorInfo) Term Arith
ruleTermArith2 =
  $(rule [p| _ |]
         [p| TFactor _ |]
         (update [p| TFactor f |]
                 [d| f = ruleFactorArith0 |])
         [| adaptTermArith |])

adaptTermArith :: BiGUL (Either ErrorInfo) Term Arith
adaptTermArith =
  CaseV [ $(adaptation [p| Mul _ _ |]
                       [p| TMul _ _ |]
                       (update [p| TMul l r |]
                               [d| l = ruleTermArith0
                                   r = ruleFactorArith0 |])
                       [| TMul TNull FNull |]),
          $(adaptation [p| Div _ _ |]
                       [p| TDiv _ _ |]
                       (update [p| TDiv l r |]
                               [d| l = ruleTermArith0
                                   r = ruleFactorArith0 |])
                       [| TDiv TNull FNull |]),
          $(adaptation [p| _ |]
                       [p| TFactor _ |]
                       (update [p| TFactor f |]
                               [d| f = ruleFactorArith0 |])
                       [| TFactor FNull |])
        ]

ruleFactorArith0 :: BiGUL (Either ErrorInfo) Factor Arith
ruleFactorArith0 =
  $(rule [p| Sub (Num 0) _ |]
         [p| FNeg _ |]
         [| $(rearr [| \((), a) -> a |])
              $(update [p| FNeg f |]
                       [d| f = ruleFactorArith0 |]) |]
         [| ruleFactorArith1 |])

ruleFactorArith1 :: BiGUL (Either ErrorInfo) Factor Arith
ruleFactorArith1 =
  $(rule [p| Num _ |]
         [p| FNum _ |]
         (update [p| FNum i |]
                 [d| i = Replace |])
         [| ruleFactorArith2 |])

ruleFactorArith2 :: BiGUL (Either ErrorInfo) Factor Arith
ruleFactorArith2 =
  $(rule [p| _ |]
         [p| FExpr _ |]
         (update [p| FExpr e |]
                 [d| e = ruleExprArith0 |])
         [| adaptFactorArith |])

adaptFactorArith :: BiGUL (Either ErrorInfo) Factor Arith
adaptFactorArith =
  CaseV [ $(adaptation [p| Sub (Num 0) _ |]
                       [p| FNeg _ |]
                       [| $(rearr [| \((), a) -> a |])
                            $(update [p| FNeg f |]
                                     [d| f = ruleFactorArith0 |]) |]
                       [| FNeg FNull |]),
          $(adaptation [p| Num _ |]
                       [p| FNum _ |]
                       (update [p| FNum i |]
                               [d| i = Replace |])
                       [| FNum 0 |]),
          $(adaptation [p| _ |]
                       [p| FExpr _ |]
                       (update [p| FExpr e |]
                               [d| e = ruleExprArith0 |])
                       [| FExpr ENull |])
        ]
