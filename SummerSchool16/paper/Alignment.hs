{-# LANGUAGE TemplateHaskell, TypeFamilies, ScopedTypeVariables #-}

module Alignment where

import Generics.BiGUL
import Generics.BiGUL.TH
import Generics.BiGUL.Lib
import Generics.BiGUL.Interpreter

import Data.Tuple
import Data.Maybe
import Data.List


--------
-- Payroll databases as lists

type Source = (Id, (Name, Salary))

type Id     = Int
type Name   = String
type Salary = Int

employees :: [Source]
employees = [ (0, ("Zhenjiang", 1000))
            , (1, ("Josh"     ,  500))
            , (2, ("Jeremy"   , 2000)) ]

type View   = (Id, Name)

bx :: BiGUL Source View
bx = $(update [p| (id, (name, _)) |] [p| (id, name) |]
              [d| id = Replace; name = Replace |])


-------
-- Positional alignment

posAlign :: (Show s, Show v)
         => BiGUL s v -> (v -> s) -> BiGUL [s] [v]
posAlign b c = Case
  [ $(normalSV [p| [] |] [p| [] |] [p| [] |])
    ==> $(update [p| [] |] [p| [] |] [d| |])
  , $(normalSV [p| _:_ |] [p| _:_ |] [p| _:_ |])
    ==> $(update [p| x:xs |] [p| x:xs |]
                 [d| x = b; xs = posAlign b c |])
  , $(adaptiveSV [p| _:_ |] [p| [] |])
    ==> \_ _ -> []
  , $(adaptiveSV [p| [] |] [p| _:_ |])
    ==> \_ (v:_) -> [c v]
  ]

-- Case
--   [ $(normalSV [p| [] |] [p| [] |] [p| [] |])
--     ==> $(update [p| [] |] [p| [] |] [d| |])
--   , $(normalSV [p| _:_ |] [p| _:_ |] [p| _:_ |])
--     ==> $(update [p| x:xs |] [p| x:xs |] [d| x = b; xs = posAlign b c |])
--   , $(adaptiveSV [p| _:_ |] [p| [] |])
--     ==> \_ _ -> []
--   , $(adaptiveSV [p| [] |] [p| _:_ |])
--     ==> \_ (v:_) -> [c v]
--   ]

cr :: View -> Source
cr (i, n) = (i, (n, 0))

-- get works fine
_ = get (posAlign bx cr) employees

-- put doesn’t quite work, though
-- delete (sack) Josh
updatedEmployees0 :: [View]
updatedEmployees0 = [(0, "Zhenjiang"), (2, "Jeremy")]

-- Jeremy gets the wrong salary
_ = put (posAlign bx cr) employees updatedEmployees0

-- reordering
updatedEmployees1 :: [View]
updatedEmployees1 = [(2, "Jeremy"), (0, "Zhenjiang"), (1, "Josh")]

-- everyone gets the wrong salary
_ = put (posAlign bx cr) employees updatedEmployees1


--------
-- Key-based alignment

keyAlign :: forall s v k. (Show s, Show v, Eq k)
         => (s -> k) -> (v -> k)
         -> BiGUL s v -> (v -> s) -> BiGUL [s] [v]
keyAlign ks kv b c = Case
  [ $(normalSV [p| [] |] [p| [] |] [p| [] |])
    ==> $(update [p| [] |] [p| [] |] [d| |])
  --
  , $(normal [| \(s:ss) (v:vs) -> ks s == kv v |] [p| _:_ |])
    ==> $(update [p| x:xs |] [p| x:xs |] [d| x = b; xs = keyAlign ks kv b c |])
  , $(adaptive [| \ss (v:vs) -> kv v `elem` map ks ss |])
    ==> \ss (v:_) -> uncurry (:) (extract (kv v) ss)
  --
  , $(adaptiveSV [p| _:_ |] [p| [] |])
    ==> \_ _ -> []
  --
  , $(adaptiveSV [p| _ |] [p| _:_ |])
    ==> \ss (v:_) -> c v : ss
  ]
  where
    extract :: k -> [s] -> (s, [s])
    extract k (x:xs) | ks x == k = (x, xs)
                     | otherwise = let (y, ys) = extract k xs
                                   in  (y, x:ys)

-- get still works properly
_ = get (keyAlign fst fst bx cr) employees

-- deletion is now handled correctly
_ = put (keyAlign fst fst bx cr) employees updatedEmployees0

-- and also reordering
_ = put (keyAlign fst fst bx cr) employees updatedEmployees1

-- id change (and reordering)
updatedEmployees2 :: [View]
updatedEmployees2 = [(0, "Zhenjiang"), (2, "Jeremy"), (100, "Josh")]

-- id change is indistinguishable from deletion and then insertion
_ = put (keyAlign fst fst bx cr) employees updatedEmployees2


--------
-- Delta-based alignment

-- pairs of associated source and view positions
-- horizontal deltas / correspondence / trace links
type Delta = [(Int, Int)]

idDelta :: [s] -> Delta
idDelta ss = [ (i, i) | i <- [0..length ss-1] ]

deltaAlign :: (Show s, Show v)
           => BiGUL s v -> (v -> s) -> BiGUL ([s], Delta) [v]
deltaAlign b c = Case
  [ $(normal [| \(ss, d) vs -> length ss == length vs && d == idDelta ss |] [p| _ |])
    ==> $(rearrS [| \(ss, _) -> ss |])$ posAlign b c
  , $(adaptive [| \_ _ -> otherwise |])
    ==> \(ss, d) vs ->
          let d'  = map swap d
              ss' = [ maybe (c v) (ss !!) (lookup j d') | (v, j) <- zip vs [0..] ]
          in (ss', idDelta ss')
  ]

putDeltaAlign :: (Show s, Show v)
              => BiGUL s v -> (v -> s) -> [s] -> Delta -> [v] -> Maybe [s]
putDeltaAlign b c ss d vs = fmap fst (put (deltaAlign b c) (ss, d) vs)

getDeltaAlign :: (Show s, Show v) => BiGUL s v -> (v -> s) -> [s] -> Maybe [v]
getDeltaAlign b c ss = get (deltaAlign b c) (ss, idDelta ss)

-- id change is fine,
-- since the source and view elements are now linked by the delta, not the id
_ = putDeltaAlign bx cr employees [(0,0), (1,2), (2,1)] updatedEmployees2

-- get still works fine
_ = getDeltaAlign bx cr employees

-- subtle updates are also possible
-- the view is unchanged but the delta says Josh is not the original Josh
_ = putDeltaAlign bx cr employees [(0,0), (2,2)] =<< getDeltaAlign bx cr employees


--------
-- Positional and key-based alignment in terms of delta-based alignment

type DeltaStrategy s v = [s] -> [v] -> Delta

putDeltaAlignS :: (Show s, Show v)
               => DeltaStrategy s v -> BiGUL s v -> (v -> s) -> [s] -> [v] -> Maybe [s]
putDeltaAlignS dst b c ss vs = putDeltaAlign b c ss (dst ss vs) vs

byPosition :: DeltaStrategy s v
byPosition ss _ = idDelta ss

_ = putDeltaAlignS byPosition bx cr employees updatedEmployees0

byKey :: Eq k => (s -> k) -> (v -> k) -> DeltaStrategy s v
byKey ks kv ss vs =
  let sis = zip ss [0..]
  in  catMaybes [ fmap (\(_, i) -> (i, j)) (find (\(s, _) -> ks s == kv v) sis)
                | (v, j) <- zip vs [0..] ]

_ = putDeltaAlignS (byKey fst fst) bx cr employees updatedEmployees1
