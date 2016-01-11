{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts, DeriveGeneric, ViewPatterns  #-}

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

xforkS :: (Eq s) => (s -> Bool) -> BiGUL [s] ([s], [s])
xforkS p = Case
  [ $(normalSV [p| [] |] [p| ([], []) |])$
      RearrV (PIn (PLeft (PConst ())) `PProd` PIn (PLeft (PConst ())))
             (EConst ()) $
      -- $(rearrV [| \([], []) -> () |])$
        Skip
  , $(normalSV [p| ((p -> True ):_) |] [p| (_:_, _) |])$
      RearrV (PIn (PRight (PVar `PProd` PVar)) `PProd` PVar)
             (EDir (DLeft (DLeft DVar)) `EProd` (EDir (DLeft (DRight DVar)) `EProd` EDir (DRight DVar))) $
      -- $(rearrV [| \(x:xs, ys) -> (x, (xs, ys)) |])$
        RearrS (PIn (PRight (PVar `PProd` PVar)))
               (EDir (DLeft DVar) `EProd` EDir (DRight DVar)) $
        -- $(rearrS [| \(s:ss) -> (s, ss) |])$
          Replace `Prod` xforkS p
  , $(normalSV [p| ((p -> False):_) |] [p| (_, _:_) |])$
      RearrV (PVar `PProd` PIn (PRight (PVar `PProd` PVar)))
             (EDir (DRight (DLeft DVar)) `EProd` (EDir (DLeft DVar) `EProd` EDir (DRight (DRight DVar)))) $
      -- $(rearrV [| \(xs, y:ys) -> (y, (xs, ys)) |])$
        RearrS (PIn (PRight (PVar `PProd` PVar)))
               (EDir (DLeft DVar) `EProd` EDir (DRight DVar)) $
        -- $(rearrS [| \(s:ss) -> (s, ss) |])$
          Replace `Prod` xforkS p
  , $(adaptiveSV [p| _ |] [p| _ |])$
      \_ (xs, ys) -> xs ++ ys
  ]

{-

---- iterative updates

iter :: Eq v => BiGUL' s v -> BiGUL' [s] v
iter bigul = Case [ $(normalS [p| [_] |]) $
                      $(rearrAndUpdate [p| v |] [p| v:_ |] [d| v = bigul |])
                  , $(normalS [p| _:_ |]) $
                      $(rearr [| \v -> (v, v) |]) $(update [p| s:ss |] [d| s = bigul; ss = iter bigul |])
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
  Case [ $(normalSV [| null . filter p |] [p| [] |]) $
           $(rearr [| \ [] -> () |]) Skip
       , $(adaptiveSV [| not . null . filter p |] [p| [] |]) $
           \ss _ -> catMaybes (map conceal ss)
       , $(normalSV [| \ss -> not (null (filter p ss)) && not (p (head ss)) |] [p| _:_ |]) $
           $(rearrAndUpdate [p| vs |] [p| _:vs |]
                            [d| vs = align p match b create conceal |])
       , $(normal' [| \ss vs -> not (null (filter p ss)) && p (head ss) && not (null vs) &&
                                match (head ss) (head vs) |]
                   [| \ss -> not (null (filter p ss)) && p (head ss) |]) $
           $(rearrAndUpdate [p| v : vs |]
                            [p| v : vs |]
                            [d| v  = b
                                vs = align p match b create conceal |])
       , $(adaptiveV [p| _:_ |]) $
           \ss (v:_) -> case find (flip match v) (filter p ss) of
                          Nothing -> create v:ss
                          Just s  -> s:delete s ss ]

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

type Name = String
type Salary = Float
type Location = String
type Employee = (Name, (Salary, Either Location Location))
type EmployeeSource = [Employee]


type EmployeeSimplified = (Name, Either Location Location)
type EmployeeView = [EmployeeSimplified]

transatlantic :: BiGUL' EmployeeSource EmployeeView
transatlantic =
  align (const True)
        (\(sName, _) (vName, _) -> sName == vName)
        ($(rearrAndUpdate
             [p| (name, rest) |] [p| (name, rest) |]
             [d| name = Replace
                 rest = Case [ $(normalSV [p| (_, Left  _) |] [p| Left  _ |]) $
                                 $(rearrAndUpdate [p| Left  loc |] [p| (_, Left  loc) |] [d| loc = Replace |])
                             , $(normalSV [p| (_, Right _) |] [p| Right _ |]) $
                                 $(rearrAndUpdate [p| Right loc |] [p| (_, Right loc) |] [d| loc = Replace |])
                             , $(adaptiveSV [p| (_, Left  _) |] [p| Right _ |]) $
                                 \(salary, _) loc -> (salary/3*5, loc)
                             , $(adaptiveSV [p| (_, Right _) |] [p| Left  _ |]) $
                                 \(salary, _) loc -> (salary/5*3, loc)
                             ] |]))
        (\(vName, location) -> (vName, (0, location)))
        (const Nothing)

employeeS :: EmployeeSource
employeeS = [ ("Jermy Gibbons", (82495, Left  "Oxford University" ))
            , ("Meng Wang"    , (13590, Left  "Oxford University" ))
            , ("Nate Foster"  , (97000, Right "Cornell University"))
            , ("Hugo Pacheco" , (35000, Right "Cornell University")) ]

getEmployee :: Either ErrorInfo EmployeeView
getEmployee = get transatlantic employeeS

-- re-ordering
-- update location
-- deletion
-- insertion
employeeView' :: EmployeeView
employeeView' = [ ("Jermy Gibbons", Left  "Cambridge University")
                , ("Nate Foster"  , Left  "Oxford University"   )
                , ("Josh Ko"      , Left  "Oxford University"   )
                , ("Meng Wang"    , Right "Havard University"   ) ]

putEmployee :: Either ErrorInfo EmployeeSource
putEmployee = put transatlantic employeeS employeeView'


---- view dependency

dep_pair :: BiGUL' (Int, Int) (Int, Int)
dep_pair = Case [ $(normalV [| \(vx, vy) -> vx == vy |]) $
                    Case [ $(normalS [| (/= 0) . snd |]) $
                             Replace
                         , $(normalS [p| _ |]) $
                             Dep ($(rearr [| \x -> (x, 0) |]) Replace)
                                 (const id)
                         ]
                , $(normalV [| (/= 0) . snd |]) $
                    Replace
                ]


---- trivial well-behaved wrapper

emb :: Eq v => (s -> v) -> (s -> v -> s) -> BiGUL' s v
emb g p = Case [ $(normal [| \x y -> g x == y |]) $
                   $(rearr [| \x -> ((), x) |]) $ Dep Skip (\x () -> g x)
               , $(adaptive [| \_ _ -> True |])
                   p
               ]

forkS :: (Eq s) => (s -> Bool) -> BiGUL' [s] ([s], [s])
forkS p = Case [ $(normalSV [p| [] |] [p| ([], []) |]) $
                   $(rearr [| \([], []) -> () |]) Skip
               , $(normalSV [p| (p -> True ):_ |] [p| (_:_, _) |]) $
                   $(rearr [| \(x:xs, ys) -> (x , (xs , ys)) |])
                     $(update [p| s:ss |] [d| s = Replace; ss = forkS p |])
               , $(normalSV [p| (p -> False):_ |] [p| (_, _:_) |]) $
                   $(rearr [| \(xs, y:ys) -> (y , (xs , ys)) |])
                     $(update [p| s:ss |] [d| s = Replace; ss = forkS p |])
               , $(adaptiveSV [p| _ |] [p| _ |]) $
                   \_ (xs, ys) -> xs ++ ys
               ]

-}
