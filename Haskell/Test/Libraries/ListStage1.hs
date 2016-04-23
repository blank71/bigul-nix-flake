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

fromJust (Just x) = x
fromJust Nothing = error "the value \"Nothing\" detected."


fromRight :: Either a b -> b
fromRight (Right x) = x
fromRight (Left _)  = error "Left detected!"