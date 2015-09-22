{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts  #-}
{- Utilities for simple resting by Zhenjiang Hu @ 22/09/2015 -}

module Util where
import Generics.BiGUL
import Control.Monad
import GHC.Generics

-- We prepare two simpler functions for testing put/get of 
-- a bigul lens; it will give the result if it succeeds and 
-- shows an error message if it fails.

testPut :: BiGUL (Either ErrorInfo) s v -> s -> v -> Either ErrorInfo s
testPut u s v = catchBind (put u s v) (\s' -> Right s') (\e -> Left e)

testGet :: BiGUL (Either ErrorInfo) s v -> s -> Either ErrorInfo v
testGet u s = catchBind (get u s) (\v' -> Right v') (\e -> Left e)
