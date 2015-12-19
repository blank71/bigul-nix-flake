{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts  #-}
{- Utilities for simple testing by Zhenjiang Hu @ 22/09/2015 -}

module Util where
import Generics.BiGUL.AST
import Generics.BiGUL.Interpreter
import Generics.BiGUL.TH
import Generics.BiGUL.MonadBiGULError
import Control.Monad
import Control.Monad.Except

-- We prepare two simpler functions for testing put/get of
-- a bigul lens; it will give the result if it succeeds and
-- shows an error message if it fails.

testPut :: BiGUL (Either ErrorInfo) s v -> s -> v -> Either ErrorInfo s
testPut u s v = catchBind (put u s v) (\s' -> Right s') (\e -> Left e)

testGet :: BiGUL (Either ErrorInfo) s v -> s -> Either ErrorInfo v
testGet u s = catchBind (get u s) (\v' -> Right v') (\e -> Left e)

-- Composion of two put lenses.

(@@) :: MonadError' ErrorInfo m => BiGUL m s x -> BiGUL m x v -> BiGUL m s v
u1 @@ u2 = Emb getc putc
  where
    getc s = do x <- get u1 s
                get u2 x
    putc s v = do x <- get u1 s
                  x' <- put u2 x v
                  put u1 s x'

-- We define a new lens to wrap Fail with additional error messages.

failMsg :: MonadError' ErrorInfo m => String -> BiGUL m s v
failMsg msg = Emb getf putf
  where
    getf s = throwError $ ErrorInfo msg
    putf s v = throwError $ ErrorInfo msg

-- Useful higher order lenses

mapU :: (Eq s, Eq v, Show v,  Monad m) => BiGUL m s v -> BiGUL m [s] [v]
mapU bigul =
  Case [ $(normalSV [p| [] |] [p| [] |]) $
           $(rearrAndUpdate [p| [] |] [p| [] |] [d| |])
       , $(normalSV [p| _:_ |] [p| _:_ |]) $
           $(rearrAndUpdate [p| x:xs |] [p| x:xs |] [d| x = bigul; xs = mapU bigul |])
       , $(adaptiveSV [p| _:_ |] [p| [] |]) $
           \_ _ -> []
       , $(adaptiveSV [p| [] |] [p| _:_ |]) $
           \_ _ -> [error "mapU"]
       ]
