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
  CaseSV [ ( (\ s v -> return $
               case s of
                 EAdd _ _ ->
                   case v of
                     Add _ _ -> True
                     _       -> False
                 _        -> False)
           , NormalSV $ ($(rearr [| \(Add l r) -> (l, r) |])
                $(update [p| EAdd el tr |]
                         [d| el = ruleExprArith0; tr = ruleTermArith0 |]))
           )
         , ( (\ s v -> return $
               case s of
                 ESub _ _ ->
                   case v of
                     Sub _ _ -> True
                     _       -> False
                 _        -> False)
           , NormalSV $ ($(rearr [| \(Sub l r) -> (l, r) |])
                $(update [p| ESub el tr |]
                         [d| el = ruleExprArith0; tr = ruleTermArith0 |]))
           )
         , ( (\ s v -> return $
               case s of
                 ETerm _ ->
                   case v of
                      _ -> True
                 _        -> False)
           , NormalSV $ ($(rearr [| \a -> a |])
                $(update [p| ETerm et |]
                         [d| et = ruleTermArith0 |]))
           )
         , ( (\s v  -> return $
               case v of
                 Add _ _ -> True
                 _       -> False)
           , AdaptiveSV $ (\_ _ -> return $ EAdd ENull TNull)
           )
         , ( (\s v  -> return $
               case v of
                 Sub _ _ -> True
                 _       -> False)
           , AdaptiveSV $ (\_ _ -> return $ ESub ENull TNull)
           )
         , ( (\s v  -> return $
               case v of
                 _ -> True)
           , AdaptiveSV $ (\_ _ -> return $ ETerm TNull)
           )
         ]


--
ruleTermArith0 :: BiGUL (Either ErrorInfo) Term Arith
ruleTermArith0 =
  CaseSV [ ( (\ s v -> return $
               case s of
                 TMul _ _ ->
                   case v of
                     Mul _ _ -> True
                     _       -> False
                 _        -> False)
           , NormalSV $ ($(rearr [| \(Mul l r) -> (l, r) |])
                $(update [p| TMul tl tr |]
                         [d| tl = ruleTermArith0; tr = ruleFactorArith0 |]))
           )
         , ( (\ s v -> return $
               case s of
                 TDiv _ _ ->
                   case v of
                     Div _ _ -> True
                     _       -> False
                 _        -> False)
           , NormalSV $ ($(rearr [| \(Div l r) -> (l, r) |])
                $(update [p| TDiv tl tr |]
                         [d| tl = ruleTermArith0; tr = ruleFactorArith0 |]))
           )
         , ( (\ s v -> return $
               case s of
                 TFactor _ ->
                   case v of
                     _ -> True
                 _        -> False)
           , NormalSV $ ($(rearr [| \a -> a |])
                $(update [p| TFactor tf |]
                         [d| tf = ruleFactorArith0 |]))
           )
         , ( (\s v  -> return $
               case v of
                 Mul _ _ -> True
                 _       -> False)
           , AdaptiveSV $ (\_ _ -> return $ TMul TNull FNull)
           )
         , ( (\s v  -> return $
               case v of
                 Div _ _ -> True
                 _       -> False)
           , AdaptiveSV $ (\_ _ -> return $ TDiv TNull FNull)
           )
         , ( (\s v  -> return $
               case v of
                 _ -> True)
           , AdaptiveSV $ (\_ _ -> return $ TFactor FNull)
           )
         ]

ruleFactorArith0 :: BiGUL (Either ErrorInfo) Factor Arith
ruleFactorArith0 =
  CaseSV [ ( (\ s v -> return $
               case s of
                 FNeg _ ->
                   case v of
                     Sub (Num 0) _ -> True
                     _       -> False
                 _        -> False)
           , NormalSV $ ($(rearr [| \(Sub (Num 0) n ) -> n |])
                $(update [p| FNeg neg |]
                         [d| neg = ruleFactorArith0 |]))
           )
         , ( (\ s v -> return $
               case s of
                 FNum _ ->
                   case v of
                     Num _ -> True
                     _     -> False
                 _      -> False)
           , NormalSV $ ($(rearr [| \(Num n) -> n |])
                $(update [p| FNum fn |]
                         [d| fn = Replace |]))
           )
         , ( (\ s v -> return $
               case s of
                 FExpr _ -> True
                 _       -> False)
           , NormalSV $ ($(rearr [| \a -> a |])
                $(update [p| FExpr fe |]
                         [d| fe = ruleExprArith0 |]))
           )
         , ( (\s v -> return $
                case v of
                  Sub (Num 0) _ -> True
                  _             -> False)
             , AdaptiveSV $ (\_ _ -> return $ FNeg FNull)
           )
         , ( (\s v -> return $
                case v of
                  Num _ -> True
                  _     -> False)
             , AdaptiveSV $ (\_ _ -> return $ FNum 0) -- maybe we can use undefined
           )
         , ( (\s v -> return $
                case v of
                  _ -> True)
             , AdaptiveSV (\_ _ -> return $ FExpr ENull)
           )
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


