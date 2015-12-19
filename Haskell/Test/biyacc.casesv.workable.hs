import GHC.Generics
import Generics.BiGUL hiding (Expr, Pat)
import Generics.BiGUL.AST hiding (Expr, Pat)
import Generics.BiGUL.TH
import Language.Haskell.TH
import BiYaccDef

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Control.Monad



testPut :: BiGUL (Either ErrorInfo) s v -> s -> v -> Either ErrorInfo s
testPut u s v = catchBind (put u s v) (\s' -> Right s') (\e -> Left e)

testGet :: BiGUL (Either ErrorInfo) s v -> s -> Either ErrorInfo v
testGet u s = catchBind (get u s) (\v' -> Right v') (\e -> Left e)

t1 = testGet ruleExprArith0 (EAdd (ETerm . TFactor . FNum $ 4 ) (TFactor (FNum 3)))
t2 = testPut ruleExprArith0 (EAdd (ETerm . TFactor . FNum $ 4 ) (TFactor (FNum 3)))

ruleExprArith0 :: BiGUL (Either ErrorInfo) Expr Arith
ruleExprArith0 =
  Case [ $(normalSV [p| EAdd _ _ |] [p| Add _ _ |] )
           $(rearrAndUpdate [p| Add l r |] [p| EAdd l r |]
                            [d| l = ruleExprArith0; r = ruleTermArith0 |])
       , $(normalSV [p| ESub _ _ |] [p| Sub _ _ |] )
           $(rearrAndUpdate [p| Sub l r |] [p| ESub l r |]
                            [d| l = ruleExprArith0; r = ruleTermArith0 |])
       , $(normalSV [p| ETerm _ |] [p|  _ |] )
           $(rearrAndUpdate [p| a  |] [p| ETerm a |]
                            [d| a = ruleTermArith0 |])
       , $(adaptiveV [p| Add _ _|]) (\_ _ -> EAdd ENull TNull)
       , $(adaptiveV [p| Sub _ _|]) (\_ _ -> ESub ENull TNull)
       , $(adaptiveV [p| _ |])      (\_ _ -> ETerm TNull)
       ]

--
ruleTermArith0 :: BiGUL (Either ErrorInfo) Term Arith
ruleTermArith0 =
  Case [ $(normalSV [p| TMul _ _ |] [p| Mul _ _ |] )
           $(rearrAndUpdate [p| Mul l r |] [p| TMul l r |]
                            [d| l = ruleTermArith0; r = ruleFactorArith0 |])
       , $(normalSV [p| TDiv _ _ |] [p| Div _ _ |] )
           $(rearrAndUpdate [p| Div l r |] [p| TDiv l r |]
                            [d| l = ruleTermArith0; r = ruleFactorArith0 |])
       , $(normalSV [p| TFactor _ |] [p|  _ |] )
           $(rearrAndUpdate [p| a  |] [p| TFactor a |]
                            [d| a = ruleFactorArith0 |])
       , $(adaptiveV [p| Mul _ _|]) (\_ _ -> TMul TNull FNull )
       , $(adaptiveV [p| Div _ _|]) (\_ _ -> TDiv TNull FNull )
       , $(adaptiveV [p| _ |])      (\_ _ -> TFactor FNull)
       ]

ruleFactorArith0 :: BiGUL (Either ErrorInfo) Factor Arith
ruleFactorArith0 =
  Case [ $(normalSV [p| FNeg _ |] [p| Sub (Num 0) _ |] )
           $(rearrAndUpdate [p| Sub (Num 0) n |] [p| FNeg n |]
                            [d| n = ruleFactorArith0 |])
       , $(normalSV [p| FNum _ |] [p| Num _ |] )
           $(rearrAndUpdate [p| Num n |] [p| FNum n |]
                            [d| n = Replace |])
       , $(normalSV [p| FExpr _ |] [p|  _ |] )
           $(rearrAndUpdate [p| a  |] [p| FExpr a |]
                            [d| a = ruleExprArith0 |])
       , $(adaptiveV [p| Sub (Num 0) _ |]) (\_ _ -> FNeg FNull)
       , $(adaptiveV [p| Num _|])          (\_ _ -> FNum 0 )
       , $(adaptiveV [p| _ |])             (\_ _ -> FExpr ENull)
       ]

-------------- quick check ---------------
-- quick check


-- putget bigul s v = do
--   s' <- testPut bigul s v
--   v' <- testGet bigul s'
--   return $ if v == v' then True else False


-- prop_GetPut :: (BiGUL (Either ErrorInfo) Expr Arith) -> Expr -> Property
prop_GetPut s = monadic runBigulM $ do
  v <- run $ testGet ruleExprArith0 s
  s' <- run $ testPut ruleExprArith0 s v
  assert $ s == s'
  where types = s :: Expr


prop_PutGet s v = monadic runBigulM $ do
  s' <- run $ testPut ruleExprArith0 s v
  v' <- run $ testGet ruleExprArith0 s'
  assert $ v == v'
  where types = (s :: Expr, v :: Arith)


runBigulM ma =
  case ma of
    Left _ -> error "cuole"
    Right a -> a


-----------
cexprg = sized cexprg'

cexprg' 0 = liftM ETerm (ctermg' 0)
cexprg' n | n > 0 =
  oneof [liftM2 EAdd subcexprg subctermg
        ,liftM2 ESub subcexprg subctermg
        ,liftM ETerm subctermg]
  where
    subcexprg = cexprg' (n `div` 2)
    subctermg = ctermg' (n `div` 2)

ctermg = sized ctermg'

ctermg' 0 = liftM TFactor (cfactorg' 0)
ctermg' n | n > 0 =
  oneof [liftM2 TMul subctermg subcfactorg
        ,liftM2 TDiv subctermg subcfactorg
        ,liftM TFactor subcfactorg]
  where
    subctermg = ctermg' (n `div` 2)
    subcfactorg = cfactorg' (n `div` 2)

cfactorg = sized cfactorg'

cfactorg' 0 = liftM FNum arbitrary
cfactorg' n | n>0 =
  oneof [liftM FNeg subcfactorg
        ,liftM FExpr subcexprg
        ,liftM FNum arbitrary]
  where
    subcfactorg = cfactorg' (n `div` 2)
    subcexprg = cexprg' (n `div` 2)

----

arithg = sized arithg'

arithg' 0 = liftM Num arbitrary
arithg' n | n > 0 =
  oneof [liftM2 Add subArithg subArithg
        ,liftM2 Sub subArithg subArithg
        ,liftM2 Mul subArithg subArithg
        ,liftM2 Div subArithg subArithg
        ,liftM Num arbitrary]
  where
    subArithg = arithg' (n `div` 2)

instance Arbitrary Expr where
  arbitrary = cexprg

instance Arbitrary Arith where
  arbitrary = arithg


-----------------


--
testArgs :: Args
testArgs = stdArgs {maxSuccess=100}

fire1 = verboseCheckWith testArgs prop_GetPut
fire2 = verboseCheckWith testArgs prop_PutGet


