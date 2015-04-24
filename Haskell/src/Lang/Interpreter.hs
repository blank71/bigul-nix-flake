{-# LANGUAGE GADTs, KindSignatures, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveGeneric #-}
module Lang.Interpreter where

import Lang.AST
import Control.Monad
import Control.Monad.Except
import GHC.InOut

put :: MonadError' ErrorInfo m => BiGUL m s v -> s -> v -> m s
put Fail s v = throwError $ ErrorInfo "update fails"
put Skip s v = return s
put Replace s v = return v
put (Update upat) s v = putPat upat s v
put (Rearr expr bigul) s v = putExpr expr v >>= put bigul s
put (Dep f bigul) s (v, v') = if f v == v' then put bigul s v else throwError $ ErrorInfo "view dependency not match"
put (CaseS branchList) s v = putCaseS branchList s v
put (CaseV branchList) s v = putCaseV branchList s v
put (Align sourceCond matchCond matchBigul create conceal) s v = putAlign sourceCond matchCond matchBigul create conceal s v


putPat :: MonadError' ErrorInfo m => UPat m s v -> s -> v -> m s
putPat (UVar bigul) s v = put bigul s v
putPat (UConst c  ) s v = if s == c then return c else throwError $ ErrorInfo "source is not a const: "
putPat (UProd upatl upatr) (sl, sr) (vl, vr) = do
  sl' <- putPat upatl sl vl
  sr' <- putPat upatr sr vr
  return (sl', sr')
--putPat (UProd _ _) _ _ = throwError $ ErrorInfo "pat not match"
putPat (ULeft upat) (Left s) v = putPat upat s v >>= \s' -> return $ Left s'
putPat (ULeft _   ) _ _ = throwError $ ErrorInfo "Either Left not match"
putPat (URight upat) (Right s) v = putPat upat s v >>= \s' -> return $ Right s'
putPat (URight _) _ _ = throwError $ ErrorInfo "Either Right not match"
putPat (UChild upat) s v = putPat upat (out s) v >>= \s' -> return $ inn s'
putPat (UElem upath upatt) (s:[]) (v, vs)  = do -- TODO: how about vs ?
  s' <- putPat upath s v
  return $ (s':[])
putPat (UElem upath upatt) (s:xs) (v, vs) = do
  s' <- putPat upath s v
  xs' <- putPat upatt xs vs
  return (s':xs')


-- Here v is more like an environment, a product.
putExpr :: MonadError' ErrorInfo m => Expr v v' -> v -> m v'
putExpr (EPath epath) v = retrieve epath v
putExpr (EConst c)    v = return c
putExpr (EChild expr) v = putExpr expr v >>= \v' -> return $ inn v'
putExpr (EProd exprl exprr) v = do
  vl' <- putExpr exprl v
  vr' <- putExpr exprr v
  return (vl', vr')
putExpr (ELeft exprl) v = putExpr exprl v >>= \v' -> return $ Left v'
--putExpr (ELeft _) _ = throwError $ ErrorInfo "ELeft not matched"
putExpr (ERight exprr) v = putExpr exprr v >>= \v' -> return $ Right v'
--putExpr (ERight _) _ = throwError $ ErrorInfo "ERight not matched"
putExpr (EElem exprh exprt) v = do
  vh <- putExpr exprh v
  vt <- putExpr exprt v
  return $ (vh: vt)


putCaseS :: MonadError' ErrorInfo m => [(s -> m Bool, CaseSBranch m s v)] -> s -> v -> m s
putCaseS [] s v = throwError $ ErrorInfo "caseS is empty"
putCaseS branches@((p, branch) : xs) s v = putCaseSHelp branches s v [] False

putCaseSHelp :: MonadError' ErrorInfo m => [(s -> m Bool, CaseSBranch m s v)] -> s -> v -> [(s -> m Bool, CaseSBranch m s v)] -> Bool -> m s
putCaseSHelp [] s v _ _ = throwError $ ErrorInfo "caseS empty with no matching pat"
putCaseSHelp branches@(x@(p, branch): xs) s v backBranches flag = p s >>=
  \b -> if b
           then
             case branch of
                  Normal bigul -> put bigul s v >>= \s' -> p s >>= \b' -> if b' then return s' else throwError $ ErrorInfo "update changes the branch."
                  Adaptive f -> if flag
                                   then throwError $ ErrorInfo "meet adaptive branch again"
                                   else f s >>= \s' -> putCaseSHelp backBranches s' v backBranches True
           else putCaseSHelp xs s v  backBranches False >>= \s' -> p s' >>= \b -> if b then throwError $ ErrorInfo "previous pat matches the updated source" else return s'


putCaseV :: MonadError' ErrorInfo m => [CaseVBranch m s v] -> s -> v -> m s
putCaseV [] s v = throwError $ ErrorInfo "caseV pattern is empty"
putCaseV (x@(CaseVBranch patv2v' bigul) :xs) s v =
  catchBind (deconstruct patv2v' v)
            (\v' -> put bigul s v')
            (\_ -> putCaseV xs s v >>= \s' -> catchBind (get bigul s') (\_ -> throwError $ ErrorInfo "get of previous caseV satisfied") (\_ -> return s'))




putAlign :: MonadError' ErrorInfo m => (s -> m Bool)
          -> (s -> v -> m Bool)
          -> BiGUL m s v
          -> (v -> m s)
          -> (s -> m (Maybe s))
          -> [s]
          -> [v]
          -> m [s]
putAlign = undefined


get :: MonadError' ErrorInfo m => BiGUL m s v -> s -> m v
get = undefined
