{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts, DeriveGeneric  #-}

import Generics.BiGUL
import Generics.BiGUL.AST
import Generics.BiGUL.TH
import Control.Monad
import GHC.Generics
--import qualified Netscape
--import qualified Xbel

main :: IO ()
main = putStrLn "Nothing to do: load the program into GHCi to test it."

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

deriveBiGULGeneric ''SBook
deriveBiGULGeneric ''VBook

s = [SBook "Real World Haskell is Not GOOD!" ["zantao"] 30.0 2015]
v = [VBook "Real World Haskell is Not GOOD!" 10.0, VBook "Learn You Haskell is GOOD!"  20.0]

bookstore :: MonadError' ErrorInfo m => BiGUL m [SBook] [VBook]
bookstore =
  Align (\_ -> return True)
        (\(SBook stitle _ _ _) (VBook vtitle _) -> return $ stitle == vtitle)
        ($(rearr [| \(VBook title price) -> (title, (), price, ()) |])
           $(update [p| SBook title _ price _ |]
                    [d| title = Replace
                        price = Replace
                        |]))
        (\(VBook vtitle vprice) -> return $ SBook vtitle [] vprice 2012 )
        (\_ -> return Nothing)

putBook :: Either ErrorInfo String
putBook = catchBind (put bookstore s v) (Right . show) Left

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
--        (Rearr (RIn (RProd RVar RVar))
--               (EProd (EDir (DLeft DVar)) (EProd (EConst ()) (EProd (EDir (DLeft DVar)) (EConst ()))))
--               (Update (UIn (UProd (UVar Replace) (UProd (UVar Skip) (UProd (UVar Replace) (UVar Skip)))))))
--        (\(VBook vtitle vprice) -> return $ SBook vtitle [] vprice 2012 )
--        (\_ -> return Nothing)
--
--putBookWithCheck :: Either ErrorInfo String
--putBookWithCheck = checkFullEmbed bookstore >>= \b ->
--  if b
--     then  catchBind (put bookstore s v) (\s' -> Right (show s')) (\e -> Left e)
--     else Left $ ErrorInfo "view variable is not fully embedded."


--top :: MonadError' ErrorInfo m =>  BiGUL m Netscape.Html Xbel.Xbel
--top = Update (UIn (UVar (
--                  Rearr (RIn RVar) (EDir DVar) (
--                    Update (UVar (
--                            Rearr RVar (EDir DVar) (
--                                Align  --TODO: source, view is not a list.
--                                  (\_ -> return True)
--                                  (\_ _ -> return True)
--                                  (
--                                     (Update (UIn (UProd
--                                       (UVar Skip)
--                                       (UIn (UProd
--                                         (UVar (Rearr (RIn (RProd (RIn Var) RVar))
--                                                      (EDir (DLeft DVar))
--                                                      Replace))
--                                         (UIn (UVar (Rearr
--                                                       (RIn (RProd (RIn Var) RVar))
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
--                                    CaseVBranch (PIn (PProd (PIn PVar) (PIn PVar)))
--                                                (Rearr (RIn (RProd (RIn RVar) (RIn RVar)))
--                                                       (EIn (EIn (EProd (EIn (EDir (DLeft DVar))) (EDir (DRight DVar))))) --TODO: check attribute representation.
--                                                       (Update (UVar Replace))),
--                                    CaseVBranch (PIn (PProd (PIn PVar) PVar))
--                                                (--caseS
--                                                  Update (UVar
--                                                         ([
--                                                           (evalPatToBool(dd...), Normal (Update (UIn (UProd
--                                                                (UVar (Rearr (PIn (PProd (PIn PVar) (PVar))) (EDir (DLeft DVar)) Replace))
--                                                                (UVar (Rearr (PIn (PProd (PIn PVar) (PVar))) (EDir (DRight DVar)) contents )))))),
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


-- Example 2: involve Adaptive
type Name = String
type Salary = Float
type Location = String
type Employee = (Name, (Salary, Either Location Location))
type EmployeeSource = [Employee]


type EmployeeSimplified = (Name, Either Location Location)
type EmployeeView = [EmployeeSimplified]

u :: MonadError' e m => BiGUL m EmployeeSource EmployeeView
u = Align (\_ -> return True)
          (\(sName, _) (vName, _) -> return (sName == vName))
          ($(rearr [| \(name, loc) -> (name, (), loc) |])
             $(update [p| (name, rest) |]
                      [d| name = Replace
                          rest = CaseV [ $(branch [p| (_, Left _) |])
                                           ($(rearr [| \(x, Left y) -> (x, y) |])
                                              (CaseS [ $(normal [p| (_, Left _) |])
                                                         $(update [p| (_, Left britLoc) |]
                                                                  [d| britLoc = Replace |]),
                                                       $(adaptive [p| (_, Right _) |])
                                                         (\(salary, _) _ -> return (salary*3/5, Left ""))
                                                     ])),
                                         $(branch [p| (_, Right _) |])
                                           ($(rearr [| \(x, Right y) -> (x, y) |])
                                              (CaseS [ $(normal   [p| (_, Right _) |])
                                                         $(update [p| (_, Right ameLoc) |]
                                                                  [d| ameLoc = Replace |]),
                                                       $(adaptive [p| (_, Left _) |])
                                                         (\(salary, _) _ -> return (salary*5/3, Right ""))
                                                     ]))
                                       ] |]))
          (\(vName, location) -> return (vName, (0, location)))
          (\_ -> return Nothing)

employeeS :: EmployeeSource
employeeS = [("Jermy Gibbons", (82495, Left "Oxford University")),
             ("Meng Wang", (13590, Left "Oxford University")),
             ("Nate Foster", (97000, Right "Cornell University")),
             ("Hugo Pacheco", (35000, Right "Cornell University"))
            ]

getEmployee = catchBind (get u employeeS) (\v -> Right (show v)) (\e -> Left e)

-- re-ordering
-- update location
-- deletion
-- insertion
employeeView' :: EmployeeView
employeeView' = [
             ("Jermy Gibbons", Left "Oxford University"),
             ("Nate Foster", Left "Oxford University"),
             ("Josh Ko", Left "Oxford University"),
             ("Meng Wang", Right "Havard University")
             ]

putEmployee :: Either ErrorInfo String
putEmployee =liftM (show) (put u employeeS employeeView')

