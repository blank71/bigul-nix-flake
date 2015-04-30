{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts  #-}

import Lang.MonadBiGULError
import Lang.AST
import Lang.Interpreter
import Control.Monad
import GHC.Generics

data SBook = SBook String [String] Double Int deriving (Show)
data VBook = VBook String Double deriving (Show)

instance Generic SBook where
  type Rep SBook = K1 R String :*: K1 R [String] :*: K1 R Double :*: K1 R Int
  from (SBook title authors price year) = K1 title :*: K1 authors :*: K1 price :*: K1 year
  to (K1 title :*: K1 authors :*: K1 price :*: K1 year) = (SBook title authors price year)

instance Generic VBook where
  type Rep VBook = K1 R String :*: K1 R Double
  from (VBook title price) = K1 title :*: K1 price
  to (K1 title :*: K1 price) = (VBook title price)


bookstore :: MonadError' ErrorInfo m => BiGUL m [SBook] [VBook]
bookstore =
  Align (\_ -> return True)
        (\(SBook stitle _ _ _) (VBook vtitle _) -> return $ stitle == vtitle)
        (Rearr (ROut (RProd RVar RVar))  --(ROut RVar)
               (EProd (EDir (DLeft DVar)) (EProd (EConst ()) (EProd (EDir (DRight DVar)) (EConst ()))))
               (Update (UOut (UProd (UVar Replace) (UProd (UVar Skip) (UProd (UVar Replace) (UVar Skip)))))))
        (\(VBook vtitle vprice) -> return $ SBook vtitle [] vprice 2012 )
        (\_ -> return Nothing)

s = [SBook "Real World Haskell is Not GOOD!" ["zantao"] 30.0 2015]
v = [VBook "Real World Haskell is Not GOOD!" 10.0, VBook "Learn You Haskell is GOOD!"  20.0]



putBook :: Either ErrorInfo String
putBook = catchBind (put bookstore s v) (\s' -> Right (show s')) (\e -> Left e)

putBook1 :: Either ErrorInfo String
putBook1 =liftM (show) (put bookstore s v)

getBook = catchBind (get bookstore s) (\v -> Right (show v)) (\e -> Left e)
