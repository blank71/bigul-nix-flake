{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts  #-}

import Lang.MonadBiGULError
import Lang.AST
import Lang.Interpreter
import Control.Monad
import GHC.Generics
import qualified Netscape
import qualified Xbel

---- 0 . iter operation test
iterBigul :: MonadError' ErrorInfo m => BiGUL m [Int] Int
iterBigul = iter Replace

putIter :: [Int] -> Int -> Either ErrorInfo [Int]
putIter s v = put iterBigul s v

getIter :: [Int] -> Either ErrorInfo Int
getIter s = get iterBigul s

---- 1. Bookstore example
data SBook = SBook String [String] Double Int deriving (Show)
data VBook = VBook String Double deriving (Show)
s = [SBook "Real World Haskell is Not GOOD!" ["zantao"] 30.0 2015]
v = [VBook "Real World Haskell is Not GOOD!" 10.0, VBook "Learn You Haskell is GOOD!"  20.0]

bookstore :: MonadError' ErrorInfo m => BiGUL m [SBook] [VBook]
bookstore =
  Align (\_ -> return True)
        (\(SBook stitle _ _ _) (VBook vtitle _) -> return $ stitle == vtitle)
        (Rearr (ROut (RProd RVar RVar))  --(ROut RVar)
               (EProd (EDir (DLeft DVar)) (EProd (EConst ()) (EProd (EDir (DRight DVar)) (EConst ()))))
               (Update (UOut (UProd (UVar Replace) (UProd (UVar Skip) (UProd (UVar Replace) (UVar Skip)))))))
        (\(VBook vtitle vprice) -> return $ SBook vtitle [] vprice 2012 )
        (\_ -> return Nothing)


instance Generic SBook where
  type Rep SBook = K1 R String :*: K1 R [String] :*: K1 R Double :*: K1 R Int
  from (SBook title authors price year) = K1 title :*: K1 authors :*: K1 price :*: K1 year
  to (K1 title :*: K1 authors :*: K1 price :*: K1 year) = (SBook title authors price year)

instance Generic VBook where
  type Rep VBook = K1 R String :*: K1 R Double
  from (VBook title price) = K1 title :*: K1 price
  to (K1 title :*: K1 price) = (VBook title price)


putBook :: Either ErrorInfo String
putBook = catchBind (put bookstore s v) (\s' -> Right (show s')) (\e -> Left e)

putBookWithCheck :: Either ErrorInfo String
putBookWithCheck = checkFullEmbed bookstore >>= \b ->
  if b
     then  catchBind (put bookstore s v) (\s' -> Right (show s')) (\e -> Left e)
     else Left $ ErrorInfo "view variable is not fully embedded."

putBook1 :: Either ErrorInfo String
putBook1 =liftM (show) (put bookstore s v)

getBook = catchBind (get bookstore s) (\v -> Right (show v)) (\e -> Left e)

checkBook :: Either ErrorInfo String
checkBook = liftM (show) (checkFullEmbed bookstore)

-- 2.  Bookstore counter example
-- The following is an example that view is  not-fully embedded,
-- With our checking, it will not be passed.
--data SBook = SBook String [String] String Int deriving (Show)
--data VBook = VBook String String deriving (Show)
--
--instance Generic SBook where
--  type Rep SBook = K1 R String :*: K1 R [String] :*: K1 R String :*: K1 R Int
--  from (SBook title authors price year) = K1 title :*: K1 authors :*: K1 price :*: K1 year
--  to (K1 title :*: K1 authors :*: K1 price :*: K1 year) = (SBook title authors price year)
--
--instance Generic VBook where
--  type Rep VBook = K1 R String :*: K1 R String
--  from (VBook title price) = K1 title :*: K1 price
--  to (K1 title :*: K1 price) = (VBook title price)
--
--
--s = [SBook "Real World Haskell is Not GOOD!" ["zantao"] "30.0" 2015]
--v = [VBook "Real World Haskell is Not GOOD!" "10.0", VBook "Learn You Haskell is GOOD!"  "20.0"]
--
--bookstore :: MonadError' ErrorInfo m => BiGUL m [SBook] [VBook]
--bookstore =
--  Align (\_ -> return True)
--        (\(SBook stitle _ _ _) (VBook vtitle _) -> return $ stitle == vtitle)
--        (Rearr (ROut (RProd RVar RVar))  --(ROut RVar)
--               (EProd (EDir (DLeft DVar)) (EProd (EConst ()) (EProd (EDir (DLeft DVar)) (EConst ()))))
--               (Update (UOut (UProd (UVar Replace) (UProd (UVar Skip) (UProd (UVar Replace) (UVar Skip)))))))
--        (\(VBook vtitle vprice) -> return $ SBook vtitle [] vprice 2012 )
--        (\_ -> return Nothing)
--
--putBookWithCheck :: Either ErrorInfo String
--putBookWithCheck = checkFullEmbed bookstore >>= \b ->
--  if b
--     then  catchBind (put bookstore s v) (\s' -> Right (show s')) (\e -> Left e)
--     else Left $ ErrorInfo "view variable is not fully embedded."


--top :: MonadError' ErrorInfo m =>  BiGUL m Netscape.Html Xbel.Xbel
--top = Update (UOut (UVar (
--                  Rearr (ROut RVar) (EDir DVar) (
--                    Update (UVar (
--                            Rearr RVar (EDir DVar) (
--                                Align  --TODO: source, view is not a list.
--                                  (\_ -> return True)
--                                  (\_ _ -> return True)
--                                  (
--                                     (Update (UOut (UProd
--                                       (UVar Skip)
--                                       (UOut (UProd
--                                         (UVar (Rearr (ROut (RProd (ROut Var) RVar))
--                                                      (EDir (DLeft DVar))
--                                                      Replace))
--                                         (UOut (UVar (Rearr
--                                                       (ROut (RProd (ROut Var) RVar))
--                                                       (EDir (DRight DVar))
--                                                       (contents) -- not supported yet.
--                                        )))
--                                      ))
--                                     )))
--                                    )
--                                  (..)
--                                  (\_ -> return Nothing)
--                              )
--                           ))
--                   )
--                  )))
--
--
--contents :: MonadError' ErrorInfo m =>  BiGUL m [(Either Netscape.Dt Netscape.Dd)] [(Either Xbel.Bookmark Xbel.Foler)]
--contents = Update (UVar (
--                    Rearr RVar
--                          (EDir DVar)
--                          (Align
--                            (\_ -> return True)
--                            (\_ _ -> return True)
--                            (Rearr RVar (EDir DVar)
--                                  (CaseV [
--                                    CaseVBranch (POut (PProd (POut PVar) (POut PVar)))
--                                                (Rearr (ROut (RProd (ROut RVar) (ROut RVar)))
--                                                       (EIn (EIn (EProd (EIn (EDir (DLeft DVar))) (EDir (DRight DVar))))) --TODO: check attribute representation.
--                                                       (Update (UVar Replace))),
--                                    CaseVBranch (POut (PProd (POut PVar) PVar))
--                                                (--caseS
--                                                  Update (UVar
--                                                         ([
--                                                           (evalPatToBool(dd...), Normal (Update (UOut (UProd
--                                                                (UVar (Rearr (POut (PProd (POut PVar) (PVar))) (EDir (DLeft DVar)) Replace))
--                                                                (UVar (Rearr (POut (PProd (POut PVar) (PVar))) (EDir (DRight DVar)) contents )))))),
--                                                           (const (return True), Adaptive (\_ -> createS(expr)) ) -- ADAPT SOURCE s -> m s
--                                                          ]))
--                                                  )
--                                  ])
--                            )
--                            (..)
--                            (\_ -> return Nothing)
--                          )
--                  ))
--



-- checkRearr :: MonadError' ErrorInfo m => Expr env v' -> RPat v env con -> m Bool


