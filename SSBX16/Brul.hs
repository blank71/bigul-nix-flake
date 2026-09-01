{-#  LANGUAGE FlexibleContexts, TemplateHaskell, TypeFamilies, ScopedTypeVariables  #-}

module Brul where

import Generics.BiGUL
import Generics.BiGUL.Interpreter
import Generics.BiGUL.TH
import Generics.BiGUL.Lib

import GHC.Generics
import Data.List
import Control.Monad.Except
import qualified Data.Map as Map
import Data.Maybe

import Alignment (employees,bx,updatedEmployees0,cr)

type RT     = [Record]
type Record = [RType]
data RType  = RInt Int
            | RString String
            | RFloat Float
            | RDouble Double
            deriving (Show, Eq, Ord)

deriveBiGULGeneric ''RType

showRType :: RType -> String
showRType (RInt i)      = show i
showRType (RString str) = str
showRType (RFloat f)    = show f
showRType (RDouble d)   = show d

tshow :: [Record] -> String
tshow []        = ""
tshow (line:ls) = tshow1 line ++ "\n" ++ tshow ls

tshow1 :: Record -> String
tshow1 []     = ""
tshow1 (r:rs) = showRType r ++ ", " ++ tshow1 rs

showTable :: [Record] -> IO ()
showTable t = putStr (tshow t)

showResult (Right t)    = showTable t
showResult (Left error) = putStrLn (show error)

showTuple :: ([Record], [Record]) -> IO ()
showTuple (s1, s2) = putStrLn "s1:" >>
                     showTable s1 >>
                     putStrLn "\ns2:" >>
                     showTable s2

showResultTuple (Right t)    = showTuple t
showResultTuple (Left error) = putStrLn (show error)

s = [ [RString "Lullaby"   , RInt 1989, RInt 3, RString "Galore"  , RInt 1]
    , [RString "Lullaby"   , RInt 1989, RInt 3, RString "Show"    , RInt 3]
    , [RString "Lovesong"  , RInt 1989, RInt 5, RString "Galore"  , RInt 1]
    , [RString "Lovesong"  , RInt 1989, RInt 5, RString "Paris"   , RInt 4]
    , [RString "Trust"     , RInt 1992, RInt 4, RString "Wish"    , RInt 5]
    ]

pAlign :: forall s v k . (Show s, Show v, Eq k)
       => (s -> Bool) --  predicate
       -> (s -> k) -> (v -> k) -> BiGUL s v -> (v -> s)
       -> (s -> Maybe s) --  conceal function
       -> BiGUL [s] [v]
pAlign p ks kv b c h = Case
  [ $(normalSV [p| [] |] [p| [] |] [p| [] |])
    ==> $(update [p| [] |] [p| [] |] [d|  |])
  , $(normal [| \(s:ss) (v:vs) -> p s && ks s == kv v |] [| \(s:ss) -> p s |])
    ==> $(update [p| x:xs |]  [p| x:xs |] [d| x = b; xs = pAlign p ks kv b c h |])
  , $(adaptive [| \(s:ss) v -> p s && null v |])
    ==> \(s:ss) v -> maybe [] (:[]) (h s) ++ ss
  , $(normal [| \(s:ss) v -> not (p s) |] [| \(s:ss) -> not (p s) |])
    ==> $(update [p| _:xs |] [p| xs |] [d| xs = pAlign p ks kv b c h |])
  , $(adaptive [| \ss (v:vs) -> kv v `elem` map ks (filter p ss) |])
    ==> \ss (v:_) -> uncurry (:) (extract (kv v) ss)
  , $(adaptiveSV [p| _ |] [p| _ :_ |])
    ==> \ss (v:_) -> filterCheck p (c v) : ss
  ]
  where
    extract :: k -> [s] -> (s, [s])
    extract k (x:xs) | p x && ks x == k = (x, xs)
                     | otherwise        = let (y, ys) = extract k xs
                                          in  (y, x:ys)
    filterCheck p v | p v       = v
                    | otherwise = error "error in filter checking"

pSelProj = pAlign (\(k,(n,s)) -> s > 1000) fst fst bx cr' (const Nothing)
  where cr' (k,n) = (k,(n, 2000))

u0   :: RType -> BiGUL [Record] [Record]
u0 d =  pAlign
          (\r -> (r !! 4) > RInt 2)
          (\s -> (s !! 0, s !! 3))
          (\v -> (v !! 0, v !! 2))
          $(update  [p| ( t : _ : r : a : q : []) |]
                    [p| ( t : r : a : q : []) |]
                    [d| t = Replace; r = Replace; a = Replace; q = Replace |])
          (\(t : r : a : q : []) -> (t : d : r : a : q : []))
          (const Nothing)

u1   :: RType -> BiGUL [Record] [Record]
u1 d =  pAlign
          (\r -> (r !! 4) > RInt 2)
          (\s -> (s !! 0, s !! 3))
          (\v -> (v !! 0, v !! 2))
          $(update [p| ( t : _ : r : a : q : []) |]
                   [p| ( t : r : a : q : []) |]
                   [d| t = Replace; r = Replace; a = Replace; q = Replace |])
          (\(t : r : a : q : []) -> (t : d : r : a : q : []))
          (\(t : d : r : a : _ : []) -> Just (t : d : r : a : RInt 0 : []))

v =  [ [RString "Lullaby" , RInt 4, RString "Show" , RInt 3]
     , [RString "Lovesong", RInt 5, RString "Paris", RInt 7]
     ]


type Brul s v = BiGUL s v
---- align operator for updating
relAlign :: (Eq a, Show a, Eq b, Show b)
      => (a -> Bool)
      -> (a -> b -> Bool)
      -> Brul a b
      -> (b -> a)
      -> (a -> Maybe a) -- conceal
      -> (a -> a)  -- update functional dependency
      -> Brul [a] [b]
relAlign p match b create conceal fd =
    Case [ $(adaptiveSV [| \ss -> null (filter p ss) && map fd ss /= ss |] [p| [] |])
        ==> \ss _ -> map (\s1 -> let s2 = fd s1 in if p s2 then berror s1 else s2) ss
        , $(adaptiveSV [| not . null . filter p |] [p| [] |])
        ==> \ss _ -> catMaybes (map (\s ->
            let s1 = if p s then conceal s else Just s
            in (maybe Nothing
                (\s1 -> let s2 = fd s1 in if p s2 then berror s1 else (Just s2)) -- after fd, check p
                s1
            )) ss) -- using fd to update
        , $(adaptiveSV [| \ss -> not (null (filter p ss)) && not (p (head ss)) && (fd (head ss) /= head ss) |] [p| _:_ |])
        ==> \(s:xs) _ -> let s1 = fd s in if p s1 then berror s else s1: xs -- after fd, check p
        , $(normalSV [| \ss -> null (filter p ss) |] [p| [] |] [| const True |])
        ==> $(update [p| _ |] [p| [] |] [d| |])
        , $(normalSV [| \ss -> not (null (filter p ss)) && not (p (head ss)) |] [p| _:_ |] [| const True |])
        ==> $(update [p| _:vs |] [p| vs |] [d| vs = relAlign p match b create conceal fd |])
        , $(normal [| \ss vs -> not (null (filter p ss)) && p (head ss) && not (null vs) && match (head ss) (head vs) |]
                    [| \ss -> not (null (filter p ss)) && p (head ss) |])
        ==> $(update [p| v: vs |] [p| v : vs |]
                        [d| v  = b
                            vs = relAlign p match b create conceal fd |])
        , $(adaptiveSV [| const True |] [p| _:_ |])
        ==> \ss (v:_) -> case find (flip match v) (filter p ss) of
                            Nothing -> let s1 = fd (create v)
                                    in if p s1
                                            then s1 :ss
                                            else berrorn s1
                            Just s  -> s :delete s ss ]

-- for showing error message.
berror s  = error $ "updated record according to functional dependency shall not satisfy p, related source record: " ++ show s
berrorn s = error $ "updated record according to functional dependency shall satisfy p, related source record: " ++ show s

-- A mapper to store the functional dependency
-- revise: many attributes may depend on the same attribute.
type FDMap = Map.Map Int [Int]

-- Mapping between source and view attribute, as brul does not support arithmetic operaiton yet, the correspondence is simply mapping.
type SVMap = Map.Map Int Int

-- update a specific location of a record with a value v with type RType.
uRecord :: Int -> RType -> Record -> Record
uRecord 0 v (x:xs) = v:xs
uRecord i v (x:xs) = x : uRecord (i-1) v xs

-- find records in the view accordign to the specific source record attribute value.
findWith :: Record -> Int -> RT -> Int -> Maybe Record
findWith rs is vs iv =
    case find p vs of
      Just r  -> Just r
      Nothing -> Nothing
  where p :: Record -> Bool
        p vr = vr !! iv == rs !! is

fd :: FDMap -> FDMap -> SVMap -> RT -> Record -> Record
fd sfdMap vfdMap svMap vs s =
  let sfdList = Map.toAscList sfdMap
  in  fdHelper sfdList vfdMap svMap vs s

fdHelper :: [(Int, [Int])] -> FDMap -> SVMap -> RT -> Record -> Record
fdHelper []                      vfdMap svMap vs s = s
fdHelper ((from, [to]): ms)      vfdMap svMap vs s =
  case Map.lookup to svMap of
    Nothing  -> fdHelper ms vfdMap svMap vs s
    Just vto ->
      case findVFrom vto vfdMap of
        Nothing    -> fdHelper ms vfdMap svMap vs s
        Just vfrom ->
          case findWith s from vs vfrom of
            Nothing -> fdHelper ms vfdMap svMap vs s
            Just rv -> let s1 = uRecord to (rv !! vto) s
                        in fdHelper ms vfdMap svMap vs s1
fdHelper ((from, (to: tos)): ms)      vfdMap svMap vs s =
  let s1 = fdHelper [(from, [to])] vfdMap svMap vs s
  in fdHelper ((from, tos): ms) vfdMap svMap vs s

findVFrom :: Int -> FDMap -> Maybe Int
findVFrom vto vfdMap =
  let vfdList = Map.toAscList vfdMap
  in findVFromHelper vto vfdList

findVFromHelper :: Int -> [(Int, [Int])] -> Maybe Int
findVFromHelper vto [] = Nothing
findVFromHelper vto ((vfrom, vtos) : vs) =
  case find (\v -> v == vto) vtos of
    Nothing -> findVFromHelper vto vs
    Just _  -> Just vfrom

--
name = 0
email = 1
location = 2
employeesFd = Map.fromList [
        (name, [email, location])
    ]
employeesVSMap = Map.fromList [
        (name, name),
        (email, email),
        (location, location)
    ]
employeesS = [
  [RString "John", RString "john@john.com", RString "Tokyo"],
  [RString "Mary", RString "mary@mary.com", RString "New York"],
  [RString "Stan", RString "stan@stan.com", RString "Tokyo"]
  ]
employeesV = [
  -- [RString "John", RString "john@john.com", RString "Tokyo"], -- delete
  -- [RString "Mary", RString "mary@mary.com", RString "New York"], -- not in view
  [RString "Stan", RString "stan@stan.com", RString "Tokyo"],
  [RString "Jeff", RString "@mjeff@jeff.com", RString "Tokyo"] -- add
  ]

uEmployeeFdFor :: [Record] -> BiGUL [Record] [Record]
uEmployeeFdFor rt =
  relAlign
    (\r -> (r !! location) == RString "Tokyo")
    (\s v -> s !! name == v !! name)
    Replace
    id
    (const Nothing)
    (fd employeesFd employeesFd employeesVSMap rt)

uEmployeeFd :: BiGUL RT RT
uEmployeeFd =
  emb (\s   -> fromJust $ get (uEmployeeFdFor []) s)
      (\s v -> fromJust $ put (uEmployeeFdFor v)  s v)

uEmployeeFdFor' :: [Record] -> BiGUL [Record] [Record]
uEmployeeFdFor' rt =
  relAlign
    (\r -> (r !! location) == RString "Tokyo")
    (\s v -> s !! name == v !! name)
    Replace
    id
    (\[name, email, location] -> Just [name, email, RString "Kyoto"])
    (fd employeesFd employeesFd employeesVSMap rt)

uEmployeeFd' :: BiGUL RT RT
uEmployeeFd' =
  emb (\s   -> fromJust $ get (uEmployeeFdFor' []) s)
      (\s v -> fromJust $ put (uEmployeeFdFor' v)  s v)


track = 0
rating = 1
album = 2
quantity = 3
trackFd = Map.fromList [
        (album, [quantity]),
        (track, [rating])
    ]
trackVSMap = Map.fromList [
        (track, track),
        (rating, rating),
        (album, album),
        (quantity, quantity)
    ]
trackS = [
    [RString "Lullaby" , RInt 3, RString "Galore", RInt 1]
  , [RString "Lullaby" , RInt 3, RString "Show"  , RInt 3]
  , [RString "Lovesong", RInt 5, RString "Galore", RInt 1]
  , [RString "Lovesong", RInt 5, RString "Paris" , RInt 4]
  , [RString "Trust"   , RInt 4, RString "Wish"  , RInt 5]
  ]
trackV = [
    -- [RString "Lullaby" , RInt 3, RString "Galore", RInt 1] -- not in view
    [RString "Lullaby" , RInt 4, RString "Show"  , RInt 3] -- update
  -- , [RString "Lovesong", RInt 5, RString "Galore", RInt 1]
  , [RString "Lovesong", RInt 5, RString "Disintegration" , RInt 7] -- update
  -- , [RString "Trust"   , RInt 4, RString "Wish"  , RInt 5] -- delete
  ]

trackSWant = [
    [RString "Lullaby" , RInt 4, RString "Galore", RInt 1] -- update by fd
  , [RString "Lullaby" , RInt 4, RString "Show"  , RInt 3] -- update
  , [RString "Lovesong", RInt 5, RString "Galore", RInt 1]
  , [RString "Lovesong", RInt 5, RString "Disintegration" , RInt 7] -- update
  -- , [RString "Trust"   , RInt 4, RString "Wish"  , RInt 5] -- delete
  ]
trackSWant' = [
    [RString "Lullaby" , RInt 4, RString "Galore", RInt 1] -- update by fd
  , [RString "Lullaby" , RInt 4, RString "Show"  , RInt 3] -- update
  , [RString "Lovesong", RInt 5, RString "Galore", RInt 1]
  , [RString "Lovesong", RInt 5, RString "Disintegration" , RInt 7] -- update
  , [RString "Trust"   , RInt 4, RString "Wish"  , RInt 1] -- conceal
  ]

uTrackFor :: RT -> BiGUL RT RT
uTrackFor v =
    relAlign
        (\r -> (r !! quantity ) > RInt 2)
        (\s v -> s !! album == v !! album && s !! track == v !! track)
        Replace
        id
        (const Nothing)
        (fd trackFd trackFd trackVSMap v)

uTrack :: BiGUL RT RT
uTrack =
    emb (\s-> fromJust $ get (uTrackFor []) s)
        (\s v ->
            fromJust $ put (uTrackFor v) s v)

uTrackFor' :: RT -> BiGUL RT RT
uTrackFor' v =
    relAlign
        (\r -> (r !! quantity ) > RInt 2)
        (\s v -> s !! album == v !! album && s !! track == v !! track)
        Replace
        id
        conceal
        (fd trackFd trackFd trackVSMap v)
  where
    conceal :: Record -> Maybe Record
    conceal s
      | any (sameTrack s) v= Nothing
      | otherwise = Just (uRecord quantity (RInt 1) s)

    sameTrack :: Record -> Record -> Bool
    sameTrack s v = s !! track == v !! track

uTrack' :: BiGUL RT RT
uTrack' =
    emb (\s-> fromJust $ get (uTrackFor' []) s)
        (\s v ->
            fromJust $ put (uTrackFor' v) s v)
