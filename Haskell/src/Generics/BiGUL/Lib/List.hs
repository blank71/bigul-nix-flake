{-# LANGUAGE ViewPatterns #-}

module Generics.BiGUL.Lib.List where

import Generics.BiGUL
import Generics.BiGUL.TH
import Generics.BiGUL.Lib

import Control.Arrow ((***))
import Data.Maybe (isJust, catMaybes)


align :: (Show a, Show b)
      => (a -> Bool)
      -> (a -> b -> Bool)
      -> BiGUL a b
      -> (b -> a)
      -> (a -> Maybe a)
      -> BiGUL [a] [b]
align p match b create conceal = Case
  [ $(normalSV [| null . filter p |] [p| [] |] [| null . filter p |])
    ==> $(rearrV [| \[] -> () |])$
          skip ()
  , $(adaptiveSV [p| _ |] [p| [] |])
    ==> \ss _ -> catMaybes (map (\s -> if p s then conceal s else Just s) ss)
  -- view is necessarily nonempty in the cases below
  , $(normalSV [p| (p -> False):_ |] [p| _ |] [p| (p -> False):(null . filter p -> False) |])
    ==> $(rearrS [| \(s:ss) -> ss |])$
          align p match b create conceal
  , $(normal [| \(s:ss) (v:vs) -> p s && match s v |] [p| (p -> True):_ |])
    ==> $(update [p| x:xs |] [p| x:xs |] [d| x = b; xs = align p match b create conceal |])
  , $(adaptive [| \ss (v:_) -> isJust (findFirst (\s -> p s && match s v) ss) ||
                               let s = create v in p s && match s v |])
    ==> \ss (v:_) -> maybe (create v:ss) (uncurry (:)) (findFirst (\s -> p s && match s v) ss)
  ]
  where
    findFirst :: (a -> Bool) -> [a] -> Maybe (a, [a])
    findFirst p [] = Nothing
    findFirst p (x:xs) | p x       = Just (x, xs)
    findFirst p (x:xs) | otherwise = fmap (id *** (x:)) (findFirst p xs)


