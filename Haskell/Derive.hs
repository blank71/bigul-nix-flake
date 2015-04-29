{-# LANGUAGE TypeOperators, TypeFamilies #-}
import GHC.Generics

data SBook = SBook String [String] Double Int deriving (Show)
data VBook = VBook String Double deriving (Show)

instance Generic SBook where
  type Rep SBook = K1 R String :*: K1 R [String] :*: K1 R Double :*: K1 R Int
  from (SBook title authors price year) = K1 title :*: K1 authors :*: K1 price :*: K1 year
  to (K1 title :*: K1 authors :*: K1 price :*: K1 year) = (SBook title authors price year)


bookstore :: MonadError' ErrorInfo m => BiGUL m [SBook] [VBook]
bookstore =
  Align (\_ -> return True)
        (\(SBook stitle _ _ _) (VBook vtitle _) -> return $ stitle == vtitle)
        (Rearr (ROut (RProd RVar RVar))  --(ROut RVar)
               (EProd (EDir (DLeft DVar)) (EProd (EConst ()) (EProd (EDir (DRight DVar)) (EConst ()))))
               (Udpate (UOut (UProd (UVar Replace) (UProd (UVar Skip) (UProd (UVar Replace) (UVar Skip))))))
        (\(VBook vtitle vprice) -> return $ SBook vtitle [] vprice 2012 )
        (\_ -> return Nothing)

