{-# LANGUAGE GADTs, KindSignatures, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveGeneric, TupleSections #-}
module Generics.BiGUL.Interpreter (put, get) where

import Generics.BiGUL.AST
import Generics.BiGUL.MonadBiGULError
import Control.Monad
import Control.Monad.Except
import GHC.InOut

put :: MonadError' ErrorInfo m => BiGUL m s v -> s -> v -> m s
put (Fail (ErrorInfo err))  s       v       = throwError $ ErrorInfo ("Fail: " ++ err)
put Skip                    s       v       = return s
put Replace                 s       v       = return v
put (Prod bigul bigul')     (s, s') (v, v') = liftM2 (,) (put bigul s v) (put bigul' s' v')
put (RearrS pat expr bigul) s       v       = do env <- deconstruct pat s
                                                 s'  <- put bigul (eval expr env) v
                                                 con <- uneval pat expr s' (emptyContainer pat)
                                                 return (construct pat (fromContainerS pat env con))
put (RearrV pat expr bigul) s       v       = deconstruct pat v >>= put bigul s . eval expr
put (Dep bigul f)           s       (v, v') = put bigul s v >>= \s' ->
                                              if f s' v == v' then return s'
                                                             else throwError $ ErrorInfo "view dependency not match"
put (Case branches)         s       v       = putCase branches s v
put (Compose bigul bigul')  s       v       = do m  <- get bigul s
                                                 m' <- put bigul' m v
                                                 put bigul s m'

getCaseBranch :: MonadError' ErrorInfo m => (s -> v -> Bool, CaseBranch m s v) -> s -> m v
getCaseBranch (p , Normal bigul q) s =
  if q s
  then do v <- get bigul s
          if p s v
          then return v
          else throwError (ErrorInfo "getCaseBranch: condition not satisfied")
  else throwError (ErrorInfo "getCaseBranch: failure predicted")
getCaseBranch (p , Adaptive f)     s = throwError (ErrorInfo "getCaseBranch: matched an adaptive branch")

putCaseCheckDiversion :: MonadError' ErrorInfo m => [(s -> v -> Bool, CaseBranch m s v)] -> s -> v -> m ()
putCaseCheckDiversion []             s v = return ()
putCaseCheckDiversion (pb@(p, b):bs) s v =
  if not (p s v)
  then catchBind (getCaseBranch pb s) (const (throwError (ErrorInfo "putCaseCheckDiversion: matched a previous branch")))
                                      (const (putCaseCheckDiversion bs s v))
  else throwError (ErrorInfo "putCaseCheckDiversion: condition not satisfied")

putCaseWithAdaptation :: MonadError' ErrorInfo m =>
                         [(s -> v -> Bool, CaseBranch m s v)] -> [(s -> v -> Bool, CaseBranch m s v)] ->
                         s -> v -> (s -> m s) -> m s
putCaseWithAdaptation []             bs' s v cont = throwError $ ErrorInfo "putCase: case exhaustion"
putCaseWithAdaptation (pb@(p, b):bs) bs' s v cont =
  if p s v
  then case b of
         Normal bigul q -> do
           s' <- put bigul s v
           if p s' v
           then if q s'
                then putCaseCheckDiversion bs' s' v >> return s'
                else throwError (ErrorInfo "putCase: incorrect branch prediction")
           else throwError (ErrorInfo "putCase: post-verification of condition failed")
         Adaptive f -> cont (f s v)
  else putCaseWithAdaptation bs (pb:bs') s v cont

putCase :: MonadError' ErrorInfo m => [(s -> v -> Bool, CaseBranch m s v)] -> s -> v -> m s
putCase bs s v = putCaseWithAdaptation bs [] s v
                   (\s' -> putCaseWithAdaptation bs [] s' v
                             (const (throwError (ErrorInfo "putCase: meeting an adaptive branch again"))))

get :: MonadError' ErrorInfo m => BiGUL m s v -> s -> m v
get (Fail (ErrorInfo err))  s       = throwError $ ErrorInfo ("Fail: " ++ err)
get Skip                    s       = return ()
get Replace                 s       = return s
get (Prod bigul bigul')     (s, s') = liftM2 (,) (get bigul s) (get bigul' s')
get (RearrS pat expr bigul) s       = deconstruct pat s >>= get bigul . eval expr
get (RearrV pat expr bigul) s       = do v'  <- get bigul s
                                         con <- uneval pat expr v' (emptyContainer pat)
                                         env <- fromContainerV pat con
                                         return (construct pat env)
get (Dep bigul f)           s       = get bigul s >>= \v -> return $ (v, f s v)
get (Case branches)         s       = getCase branches s
get (Compose bigul1 bigul2) s       = get bigul1 s >>= get bigul2

getCase :: MonadError' ErrorInfo m => [(s -> v -> Bool, CaseBranch m s v)] -> s -> m v
getCase []             s = throwError $ ErrorInfo "getCase: case exhaustion"
getCase (pb@(p, b):bs) s =
  catchBind (getCaseBranch pb s) return
            (const (do v <- getCase bs s
                       if not (p s v)
                       then return v
                       else throwError (ErrorInfo "getCase: matched a previous branch")))
