{-# LANGUAGE GADTs, KindSignatures, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveGeneric, TupleSections #-}
module Generics.BiGUL.Interpreter (put, get) where

import Generics.BiGUL.AST
import Generics.BiGUL.MonadBiGULError
import Control.Monad
import Control.Monad.Except
import GHC.InOut
import Data.Maybe (catMaybes)
import Data.Foldable
import Control.Arrow

put :: MonadError' ErrorInfo m => BiGUL m s v -> s -> v -> m s
put Fail s v = throwError $ ErrorInfo "update fails"
put Skip s v = return s
put Replace s v = return v
put (Update upat) s v = putUPat upat s v
put (Rearr rpat expr bigul) s v = deconstructR rpat v >>= put bigul s . eval expr
put (Dep f bigul) s (v, v') = put bigul s v >>= \s' ->
                              if f s' v == v' then return s' else throwError $ ErrorInfo "view dependency not match"
put (Case branches) s v = putCase branches s v
put (Emb g p) s v = p s v
put (Compose bigul1 bigul2) s v = do u <- get bigul1 s
                                     u2 <- put bigul2 u v
                                     put bigul1 s u2

putUPat :: MonadError' ErrorInfo m => UPat m s v -> s -> v -> m s
putUPat (UVar bigul) s v = put bigul s v
putUPat (UConst c  ) s v = if s == c then return c else throwError $ ErrorInfo "source is not a const: "
putUPat (UProd upatl upatr) (sl, sr) (vl, vr) = liftM2 (,) (putUPat upatl sl vl) (putUPat upatr sr vr)
putUPat (ULeft upat) (Left s) v = liftM Left (putUPat upat s v)
putUPat (ULeft _   ) _ _ = throwError $ ErrorInfo "Either Left not match"
putUPat (URight upat) (Right s) v = liftM Right (putUPat upat s v)
putUPat (URight _) _ _ = throwError $ ErrorInfo "Either Right not match"
putUPat (UIn upat) s v = liftM inn (putUPat upat (out s) v)
putUPat (UElem upath upatt) [] (v, vs)  = throwError $ ErrorInfo "UElem pat not match"
putUPat (UElem upath upatt) (s:xs) (v, vs) = liftM2 (:) (putUPat upath s v) (putUPat upatt xs vs)

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
get Fail s = throwError $ ErrorInfo "get fail operator"
get Skip s = return $ ()
get Replace s = return s
get (Update upat) s = getUPat upat s
get (Rearr rpat expr bigul) s = get bigul s >>= \v' -> uneval rpat expr v' (emptyContainer rpat) >>= constructR rpat
get (Dep f bigul) s = get bigul s >>= \v -> return $ (v, f s v)
get (Case branches) s = getCase branches s
get (Compose bigul1 bigul2) s = get bigul1 s >>= get bigul2
get (Emb g p) s = g s

getUPat :: MonadError' ErrorInfo m => UPat m s v -> s -> m v
getUPat (UVar bigul) s = get bigul s
getUPat (UConst c  ) s = if c== s then return () else throwError $ ErrorInfo "source is not a constant."
getUPat (UProd upatl upatr) (s, s') = liftM2 (,) (getUPat upatl s) (getUPat upatr s')
getUPat (ULeft  upat) (Left s)  = getUPat upat s
getUPat (ULeft  upat) _         = throwError $ ErrorInfo "ULeft pat not match"
getUPat (URight upat) (Right s) = getUPat upat s
getUPat (URight upat) _         = throwError $ ErrorInfo "URight pat not match"
getUPat (UIn    upat) s          = getUPat upat (out s)
getUPat (UElem upath upatt) []  = throwError $ ErrorInfo "UElem cannot accept empty source list"
getUPat (UElem upath upatt) (x: xs) = liftM2 (,) (getUPat upath x) (getUPat upatt xs)

getCase :: MonadError' ErrorInfo m => [(s -> v -> Bool, CaseBranch m s v)] -> s -> m v
getCase []             s = throwError $ ErrorInfo "getCase: case exhaustion"
getCase (pb@(p, b):bs) s =
  catchBind (getCaseBranch pb s) return
            (const (do v <- getCase bs s
                       if not (p s v)
                       then return v
                       else throwError (ErrorInfo "getCase: matched a previous branch")))
