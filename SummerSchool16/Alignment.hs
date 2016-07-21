{-# LANGUAGE TemplateHaskell, TypeFamilies, ScopedTypeVariables #-}

import Generics.BiGUL
import Generics.BiGUL.TH
import Generics.BiGUL.Lib
import Generics.BiGUL.Interpreter

import Data.Tuple
import Data.Maybe
import Data.List


type Id     = Int
type Name   = String
type Salary = Int

type Source = (Id, (Name, Salary))
type View   = (Id, Name)

bx :: BiGUL Source View
bx = Replace `Prod` $(rearrS [| \(n, _) -> n |]) Replace


-------
-- Positional alignment

cr :: View -> Source
cr (i, n) = (i, (n, 0))

posAlign :: (Show s, Show v) => BiGUL s v -> (v -> s) -> BiGUL [s] [v]
posAlign b c = Case
  [ $(normalSV [p| [] |] [p| [] |] [p| [] |])
    ==> $(update [p| [] |] [p| [] |] [d| |])
  , $(normalSV [p| _:_ |] [p| _:_ |] [p| _:_ |])
    ==> $(update [p| x:xs |] [p| x:xs |] [d| x = b; xs = posAlign b c |])
  , $(adaptiveSV [p| _:_ |] [p| [] |])
    ==> \_ _ -> []
  , $(adaptiveSV [p| [] |] [p| _:_ |])
    ==> \_ (v:_) -> [c v]
  ]

employees :: [Source]
employees = [(0, ("Zhenjiang", 1000)), (1, ("Josh", 400)), (2, ("Jeremy", 2000))]

_ = get (posAlign bx cr) employees
-- Just [(0,"Zhenjiang"),(1,"Josh"),(2,"Jeremy")]

updatedEmployees0 :: [View]
updatedEmployees0 = [(0, "Zhenjiang"), (2, "Jeremy")]

_ = put (posAlign bx cr) employees updatedEmployees0
-- Just [(0,("Zhenjiang",1000)),(2,("Jeremy",400))]

updatedEmployees1 :: [View]
updatedEmployees1 = [(2, "Jeremy"), (0, "Zhenjiang"), (1, "Josh")]

_ = put (posAlign bx cr) employees updatedEmployees1
-- Just [(2,("Jeremy",1000)),(0,("Zhenjiang",400)),(1,("Josh",2000))]


--------
-- Key-based alignment

keyAlign :: forall s v k. (Show s, Show v, Eq k)
         => (s -> k) -> (v -> k) -> BiGUL s v -> (v -> s) -> BiGUL [s] [v]
keyAlign ks kv b c = Case
  [ $(normalSV [p| [] |] [p| [] |] [p| [] |])
    ==> $(update [p| [] |] [p| [] |] [d| |])
  , $(normal [| \(s:ss) (v:vs) -> ks s == kv v |] [p| _:_ |])
    ==> $(update [p| x:xs |] [p| x:xs |] [d| x = b; xs = keyAlign ks kv b c |])
  , $(adaptiveSV [p| _:_ |] [p| [] |])
    ==> \_ _ -> []
  , $(adaptive [| \ss (v:vs) -> kv v `elem` map ks ss |])
    ==> \ss (v:_) -> uncurry (:) (extract (kv v) ss)
  , $(adaptiveSV [p| _ |] [p| _:_ |])
    ==> \ss (v:_) -> c v : ss
  ]
  where
    extract :: k -> [s] -> (s, [s])
    extract k (x:xs) | ks x == k = (x, xs)
                     | otherwise = let (y, ys) = extract k xs
                                   in  (y, x:ys)

_ = get (keyAlign fst fst bx cr) employees
-- Just [(0,"Zhenjiang"),(1,"Josh"),(2,"Jeremy")]

_ = put (keyAlign fst fst bx cr) employees updatedEmployees0
-- Just [(0,("Zhenjiang",1000)),(2,("Jeremy",2000))]

_ = put (keyAlign fst fst bx cr) employees updatedEmployees1
-- Just [(1,("Josh",400)),(0,("Zhenjiang",1000)),(2,("Jeremy",2000))]

updatedEmployees2 :: [View]
updatedEmployees2 = [(0, "Zhenjiang"), (100, "Josh"), (1, "Jeremy")]

_ = put (keyAlign fst fst bx cr) employees updatedEmployees2
-- Just [(0,("Zhenjiang",1000)),(1,("Jeremy",400)),(100,("Josh",0))]


--------
-- Delta-based alignment

type Delta = [(Int, Int)]  -- pairs of associated source and view positions

idDelta :: [s] -> Delta
idDelta ss = [ (i, i) | i <- [0..length ss] ]

deltaAlign :: (Show s, Show v) => BiGUL s v -> (v -> s) -> BiGUL ([s], Delta) [v]
deltaAlign b c = Case
  [ $(normal [| \(ss, d) vs -> length ss == length vs && d == idDelta ss |] [p| _ |])
    ==> $(rearrS [| \(ss, _) -> ss |])$ posAlign b c
  , $(adaptive [| \_ _ -> otherwise |])
    ==> \(ss, d) vs -> let d'  = map swap d
                           ss' = [ maybe (c v) (ss !!) (lookup j d') | (v, j) <- zip vs [0..] ]
                       in (ss', idDelta ss')
  ]

putDeltaAlign :: (Show s, Show v) => BiGUL s v -> (v -> s) -> [s] -> Delta -> [v] -> Maybe [s]
putDeltaAlign b c ss d vs = fmap fst (put (deltaAlign b c) (ss, d) vs)

getDeltaAlign :: (Show s, Show v) => BiGUL s v -> (v -> s) -> [s] -> Maybe [v]
getDeltaAlign b c ss = get (deltaAlign b c) (ss, idDelta ss)

_ = putDeltaAlign bx cr employees [(0,0), (1,2), (2,1)] updatedEmployees2
-- Just [(0,("Zhenjiang",1000)),(1,("Jeremy",2000)),(100,("Josh",400))]

_ = getDeltaAlign bx cr employees
-- Just [(0,"Zhenjiang"),(1,"Josh"),(2,"Jeremy")]

_ = putDeltaAlign bx cr employees [(0,0), (2,2)] =<< getDeltaAlign bx cr employees
-- Just [(0,("Zhenjiang",1000)),(1,("Josh",0)),(2,("Jeremy",2000))]

type DeltaStrategy s v = [s] -> [v] -> Delta

putDeltaAlignS :: (Show s, Show v) => DeltaStrategy s v -> BiGUL s v -> (v -> s) -> [s] -> [v] -> Maybe [s]
putDeltaAlignS dst b c ss vs = putDeltaAlign b c ss (dst ss vs) vs

byPosition :: DeltaStrategy s v
byPosition ss _ = idDelta ss

_ = putDeltaAlignS byPosition bx cr employees updatedEmployees0
-- Just [(0,("Zhenjiang",1000)),(2,("Jeremy",400))]

byKey :: Eq k => (s -> k) -> (v -> k) -> DeltaStrategy s v
byKey ks kv ss vs = let sis = zip ss [0..]
                    in  catMaybes [ fmap (\(_, i) -> (i, j)) (find (\(s, _) -> ks s == kv v) sis)
                                  | (v, j) <- zip vs [0..] ]

_ = putDeltaAlignS (byKey fst fst) bx cr employees updatedEmployees1
-- Just [(1,("Josh",400)),(0,("Zhenjiang",1000)),(2,("Jeremy",2000))]
