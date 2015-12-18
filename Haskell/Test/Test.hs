{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts, DeriveGeneric  #-}

import Generics.BiGUL
import Generics.BiGUL.AST
import Generics.BiGUL.TH
import Control.Monad
import Data.Char
import Data.Maybe
import Data.List
import GHC.Generics
--import qualified Netscape
--import qualified Xbel


main :: IO ()
main = putStrLn "Nothing to do: load the program into GHCi to test it."


type BiGUL' s v = BiGUL (Either ErrorInfo) s v


---- iterative updates

iter :: Eq v => BiGUL' s v -> BiGUL' [s] v
iter bigul = Case [ ((\ss _ -> length ss == 1),
                     Normal $(rearrAndUpdate [p| v |] [p| v:_ |] [d| v = bigul |])
                       ((== 1) . length))
                  , ((\ss _ -> not (null ss)),
                     Normal ($(rearr [| \v -> (v, v) |]) $(update [p| s:ss |] [d| s = bigul; ss = iter bigul |]))
                       (not . null))
                  ]

iterBigul :: BiGUL' [Int] Int
iterBigul = iter Replace

putIter :: [Int] -> Int -> Either ErrorInfo [Int]
putIter s v = put iterBigul s v

getIter :: [Int] -> Either ErrorInfo Int
getIter s = get iterBigul s


---- list alignment

align :: (Eq a, Eq b)
      => (a -> Bool)
      -> (a -> b -> Bool)
      -> BiGUL' a b
      -> (b -> a)
      -> (a -> Maybe a)
      -> BiGUL' [a] [b]
align p match b create conceal =
  Case [ ((\ss vs -> null (filter p ss) && null vs),
          Normal ($(rearr [| \ [] -> () |]) Skip)
            (null . filter p))
       , ((\ss vs -> not (null (filter p ss)) && null vs),
          Adaptive (\ss _ -> catMaybes (map conceal ss)))
       , ((\ss vs -> not (null (filter p ss)) && not (null vs) && not (p (head ss))),
          Normal ($(rearrAndUpdate [p| vs |] [p| _:vs |]
                                   [d| vs = align p match b create conceal |]))
            (\ss -> not (null (filter p ss)) && not (p (head ss))))
       , ((\ss vs -> not (null (filter p ss)) && not (null vs) && p (head ss) &&
                     match (head ss) (head vs)) ,
          Normal ($(rearrAndUpdate [p| v : vs |]
                                   [p| v : vs |]
                                   [d| v  = b
                                       vs = align p match b create conceal |]))
            (\ss -> not (null (filter p ss)) && p (head ss)))
       , ((\ss vs -> not (null vs)),
          Adaptive (\ss (v:_) ->
                      case find (flip match v) (filter p ss) of
                        Nothing -> create v:ss
                        Just s  -> s:delete s ss)) ]

testAlign :: BiGUL' [(Int, Char)] [Int]
testAlign = align (isUpper . snd)
                  (\(ks, _) v -> ks == v)
                  ($(rearrAndUpdate [p| v |] [p| (v, _) |] [d| v = Replace |]))
                  (\v -> (v, 'X'))
                  (\(k, c) -> Just (k, toLower c))


---- bookstore example

data SBook = SBook String [String] Double Int deriving (Show, Eq)
data VBook = VBook String Double deriving (Show, Eq)

deriveBiGULGeneric ''SBook
deriveBiGULGeneric ''VBook

s = [SBook "Real World Haskell is Not GOOD!" ["zantao"] 30.0 2015]
v = [VBook "Real World Haskell is Not GOOD!" 10.0, VBook "Learn You Haskell is GOOD!"  20.0]

bookstore :: BiGUL' [SBook] [VBook]
bookstore =
  align (const True)
        (\(SBook stitle _ _ _) (VBook vtitle _) -> stitle == vtitle)
        ($(rearrAndUpdate [p| VBook title price |]
                          [p| SBook title _ price _ |]
                          [d| title = Replace
                              price = Replace |]))
        (\(VBook vtitle vprice) -> SBook vtitle [] vprice 2012)
        (const Nothing)

putBook :: Either ErrorInfo [SBook]
putBook = put bookstore s v

putBookWithCheck :: Either ErrorInfo [SBook]
putBookWithCheck = do
  b <- checkFullEmbed bookstore
  if b
  then putBook
  else Left (ErrorInfo "view variable is not fully embedded.")

getBook :: Either ErrorInfo [VBook]
getBook = get bookstore s

checkBook :: Either ErrorInfo Bool
checkBook = checkFullEmbed bookstore


---- transatlantic corporation

-- type Name = String
-- type Salary = Float
-- type Location = String
-- type Employee = (Name, (Salary, Either Location Location))
-- type EmployeeSource = [Employee]


-- type EmployeeSimplified = (Name, Either Location Location)
-- type EmployeeView = [EmployeeSimplified]

-- transatlantic :: MonadError' e m => BiGUL m EmployeeSource EmployeeView
-- transatlantic =
--   align (const True)
--         (\(sName, _) (vName, _) -> sName == vName)
--         ($(rearr [| \(name, loc) -> (name, (), loc) |])
--            $(update [p| (name, rest) |]
--                     [d| name = Replace
--                         rest = CaseV [ $(branch [p| (_, Left _) |])
--                                          ($(rearr [| \(x, Left y) -> (x, y) |])
--                                             (CaseS [ $(normal [p| (_, Left _) |])
--                                                        $(update [p| (_, Left britLoc) |]
--                                                                 [d| britLoc = Replace |]),
--                                                      $(adaptive [p| (_, Right _) |])
--                                                        (\(salary, _) _ -> return (salary*3/5, Left ""))
--                                                    ])),
--                                        $(branch [p| (_, Right _) |])
--                                          ($(rearr [| \(x, Right y) -> (x, y) |])
--                                             (CaseS [ $(normal   [p| (_, Right _) |])
--                                                        $(update [p| (_, Right ameLoc) |]
--                                                                 [d| ameLoc = Replace |]),
--                                                      $(adaptive [p| (_, Left _) |])
--                                                        (\(salary, _) _ -> return (salary*5/3, Right ""))
--                                                    ]))
--                                      ] |]))
--         (\(vName, location) -> return (vName, (0, location)))
--         (\_ -> return Nothing)

-- employeeS :: EmployeeSource
-- employeeS = [("Jermy Gibbons", (82495, Left "Oxford University")),
--              ("Meng Wang", (13590, Left "Oxford University")),
--              ("Nate Foster", (97000, Right "Cornell University")),
--              ("Hugo Pacheco", (35000, Right "Cornell University"))
--             ]

-- getEmployee = catchBind (get u employeeS) (\v -> Right (show v)) (\e -> Left e)

-- -- re-ordering
-- -- update location
-- -- deletion
-- -- insertion
-- employeeView' :: EmployeeView
-- employeeView' = [
--              ("Jermy Gibbons", Left "Oxford University"),
--              ("Nate Foster", Left "Oxford University"),
--              ("Josh Ko", Left "Oxford University"),
--              ("Meng Wang", Right "Havard University")
--              ]

-- putEmployee :: Either ErrorInfo String
-- putEmployee =liftM (show) (put u employeeS employeeView')


---- view dependency

dep_pair :: BiGUL (Either ErrorInfo) (Int, Int) (Int, Int)
dep_pair = Case [ ((\_ (vx, vy) -> vx == vy) ,
                   Normal (Case [ ((\(_, sy) _ -> sy /= 0), Normal Replace ((/= 0) . snd))
                                , ((\_ _ -> True)        , Normal (Dep (const id) ($(rearr [| \x -> (x, 0) |]) Replace)) (const True)) ])
                     (const True))
                , ((\_ (_, vy) -> vy /= 0) ,
                   Normal Replace
                     (const True)) ]

---- summative distribution

distribute :: ([Int] -> Int -> [Int]) -> BiGUL' [Int] Int
distribute f = Case [ ((\xs x -> sum xs == x),
                       Normal ($(rearr [| \x -> ((), x) |]) $ Dep (\xs () -> sum xs) Skip) (const True))
                    , ((\_ _ -> True), Adaptive f) ]
