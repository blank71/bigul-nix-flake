{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module ListStage1 where

import Generics.BiGUL.AST
import Generics.BiGUL.Interpreter
import Language.Haskell.TH as TH hiding (Name)
import Generics.BiGUL.TH


replaceByPosition :: BiGUL [a] [a]
replaceByPosition = Case  [ $(normalSV [p| [] |] [p| [] |] )
                              $(update [p| [] |] [p| [] |] [d| |])
                          , $(normalSV [p| _:_ |] [p| _:_ |] )
                              $(update [p| x:xs |] [p| x:xs |] [d| x = Replace; xs = replaceByPosition |])
                     ]




-- work on non-empty list, remove the first maximum value
removeMaximum :: (Ord a) => [a] -> [a]
removeMaximum [x] = []
removeMaximum xs = let m = maximum xs in takeWhile (/= m) xs ++ tail (dropWhile (/= m) xs)

secondMax :: (Ord a) => [a] -> a
secondMax [x] = x
secondMax xs = maximum (removeMaximum xs)

removeMinimum :: (Ord a) => [a] -> [a]
removeMinimum [x] = []
removeMinimum xs = let m = minimum xs in takeWhile (/= m) xs ++ tail (dropWhile (/= m) xs)

secondMin :: (Ord a) => [a] -> a
secondMin [x] = x
secondMin xs = minimum (removeMinimum xs)




fromJust (Just x) = x
fromJust Nothing = error "the value \"Nothing\" detected."


fromRight :: Either a b -> b
fromRight (Right x) = x
fromRight (Left _)  = error "Left detected!"

sameElems :: (Eq a) => a -> [a] -> Bool
sameElems _ [] = True
sameElems x xs = and $ map (== x) xs

sameElems' :: (Eq a) => [a] -> Bool
sameElems' [] = True
sameElems' (x:xs) = sameElems x xs