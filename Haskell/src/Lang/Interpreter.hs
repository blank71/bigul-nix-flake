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
put (Update upat) s v = putUPat upat s v
put (Rearr pat expr bigul) s v = deconstruct pat v >>= putExpr expr  >>= put bigul s
put (Dep f bigul) s (v, v') = if f v == v' then put bigul s v else throwError $ ErrorInfo "view dependency not match"
put (CaseS branchList) s v = putCaseS branchList s v
put (CaseV branchList) s v = putCaseV branchList s v
put (Align sourceCond matchCond matchBigul create conceal) s v = putAlign sourceCond matchCond matchBigul create conceal s v


putUPat :: MonadError' ErrorInfo m => UPat m s v -> s -> v -> m s
putUPat (UVar bigul) s v = put bigul s v
putUPat (UConst c  ) s v = if s == c then return c else throwError $ ErrorInfo "source is not a const: "
putUPat (UProd upatl upatr) (sl, sr) (vl, vr) = do
  sl' <- putUPat upatl sl vl
  sr' <- putUPat upatr sr vr
  return (sl', sr')
putUPat (ULeft upat) (Left s) v = putUPat upat s v >>= \s' -> return $ Left s'
putUPat (ULeft _   ) _ _ = throwError $ ErrorInfo "Either Left not match"
putUPat (URight upat) (Right s) v = putUPat upat s v >>= \s' -> return $ Right s'
putUPat (URight _) _ _ = throwError $ ErrorInfo "Either Right not match"
putUPat (UChild upat) s v = putUPat upat (out s) v >>= \s' -> return $ inn s'
putUPat (UElem upath upatt) (s:[]) (v, vs)  = do -- TODO: how about vs ?
  s' <- putUPat upath s v
  return $ (s':[])
putUPat (UElem upath upatt) (s:xs) (v, vs) = do
  s' <- putUPat upath s v
  xs' <- putUPat upatt xs vs
  return (s':xs')


-- Here v is more like an environment, a product.
putExpr :: MonadError' ErrorInfo m => Expr v v' -> v -> m v'
putExpr (EPath epath) v = return $ retrieve epath v
putExpr (EConst c)    v = return c
putExpr (EChild expr) v = putExpr expr v >>= \v' -> return $ inn v'
putExpr (EProd exprl exprr) v = do
  vl' <- putExpr exprl v
  vr' <- putExpr exprr v
  return (vl', vr')
putExpr (ELeft exprl) v = putExpr exprl v >>= \v' -> return $ Left v'
putExpr (ERight exprr) v = putExpr exprr v >>= \v' -> return $ Right v'
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




putAlign :: MonadError' ErrorInfo m =>
             (s -> m Bool)
          -> (s -> v -> m Bool)
          -> BiGUL m s v
          -> (v -> m s)
          -> (s -> m (Maybe s))
          -> [s]
          -> [v]
          -> m [s]
putAlign sourceCond matchCond matchBigul create conceal ss vs =
  filterSourceList sourceCond ss >>= \(filtered, residual) ->
    align vs filtered sourceCond matchCond matchBigul create conceal >>= \(concealed, synced) ->  return (unfilterP (concealed ++ synced) residual)
-- put the unmatched source on the top, and this will not affect matched element for view.

-- Filter tries to remember the location.
filterSourceList :: MonadError' ErrorInfo m => (s -> m Bool) -> [s] -> m ([s], [Maybe s])
filterSourceList p [] = return $ ([], [])
filterSourceList p (s: ss) = p s >>= \b -> liftM (\(ls, rs) -> if b then (s:ls, (Nothing: rs)) else (ls, (Just s) :rs)) (filterSourceList p ss)


align :: MonadError' ErrorInfo m => [v] -> [s] ->
             (s -> m Bool)
          -> (s -> v -> m Bool)
          -> BiGUL m s v
          -> (v -> m s)
          -> (s -> m (Maybe s))
          -> m ([s], [s])
align [] ss sourceCond matchCond matchBigul create conceal = liftM (flip (,) []) $ concealSourceList ss sourceCond conceal
align vss@(v:vs) [] sourceCond matchCond matchBigul create conceal = liftM ((,) []) $ createSourceList vss create sourceCond (put matchBigul) matchCond
align (v:vs) sss@(s:ss) sourceCond matchCond matchBigul create conceal = firstMatch v sss matchCond >>=
            maybe (liftM2 (\h (uss, mss) -> (uss, h:mss)) (createAndCheck v create sourceCond (put matchBigul) matchCond) (align vs sss sourceCond matchCond matchBigul create conceal))
                  (\(matchedS, sRest) -> putAndCheck matchedS v sourceCond (put matchBigul) matchCond >>= \s' -> liftM (\(uss, mss) -> (uss, s': mss)) (align vs sRest sourceCond matchCond matchBigul create conceal))



-- for a list of unmatched source, make them disappear in the view.
-- Make this list disappear by unsatisfying the condition.
-- foldM :: Monad m => (a -> b -> m a) -> a -> [b] -> m a
concealSourceList :: MonadError' ErrorInfo m => [s] -> (s -> m Bool) -> (s -> m (Maybe s)) -> m [s]
concealSourceList ss p conceal = foldM (\ls s -> conceal s >>= \ms' -> case ms' of {Just s' -> p s' >>= \b -> if b then throwError $ ErrorInfo "shall not satisfy cond anymore" else return (ls ++ [s']) ; Nothing -> return ls}) [] ss

-- for a list of unmatched view, create a source list.
createSourceList :: MonadError' ErrorInfo m => [v] -> (v -> m s) -> (s -> m Bool) -> (s -> v -> m s) -> (s -> v -> m Bool) -> m [s]
createSourceList []      create p elemPut matchCond = return []
createSourceList (v: vs) create p elemPut matchCond = liftM2 (\h t -> h : t) (createAndCheck v create p elemPut matchCond) (createSourceList vs create p elemPut matchCond)

createAndCheck :: MonadError' ErrorInfo m => v -> (v -> m s) -> (s -> m Bool) -> (s -> v -> m s) -> (s -> v -> m Bool)-> m s
createAndCheck v create p elemPut  matchCond = create v >>= \s -> putAndCheck s v p elemPut matchCond


putAndCheck :: MonadError' ErrorInfo m => s -> v -> (s -> m Bool) -> (s -> v -> m s) -> (s -> v -> m Bool)-> m s
putAndCheck s v p elemPut matchCond = elemPut s v
                                      >>= \s' -> matchCond s' v
                                      >>= \b -> if b
                                              then p s' >>= \b' ->
                                                  if b' then return s' else throwError $ ErrorInfo "created source not satisfy the source filter condition"
                                              else throwError $ ErrorInfo "created source not aligned with the matched view"



firstMatch :: MonadError' ErrorInfo m => v -> [s] -> (s -> v -> m Bool) -> m (Maybe (s, [s]))
firstMatch v []      matchCond = return Nothing
firstMatch v (s: ss) matchCond =
  matchCond s v >>= \b -> if b
                  then return (Just (s, ss))
                  else liftM (\mtuple -> case mtuple of {Just (s1, slast) -> Just (s1, s:slast); Nothing -> Nothing }) (firstMatch v ss matchCond)


unfilterP :: [s] -> [Maybe s] -> [s]
unfilterP xs [] = xs
unfilterP [] myss@(my: mys) = condense myss
unfilterP (x: xs) (Nothing : mys) = x : unfilterP xs mys
unfilterP xss@(x: xs) (Just y  : mys) = y : unfilterP xss mys


condense :: [Maybe s] ->[s]
condense [] = []
condense (Nothing : mxs) = condense mxs
condense (Just s: mxs) = s: condense mxs

get :: MonadError' ErrorInfo m => BiGUL m s v -> s -> m v
get Fail s = throwError $ ErrorInfo "get failed"
get Skip s = return $ ()
get Replace s = return s
get (Update upat) s = getUPat upat s
get (Rearr pat expr bigul) s = liftM (construct pat) (get bigul s >>= getExpr pat expr)
get (Dep f bigul) s = get bigul s >>= \v -> return $ (v, f v)
get (CaseS sbranches) s = getCaseS sbranches s
get (CaseV vbranches) s = getCaseV vbranches s
get (Align sourceCond matchCond matchBigul create conceal) s = getAlign sourceCond matchCond matchBigul create conceal s



getUPat :: MonadError' ErrorInfo m => UPat m s v -> s -> m v
getUPat (UVar bigul) s = get bigul s --TODO
getUPat (UConst c  ) s = return ()
getUPat (UProd upatl upatr) (s, s') = liftM2 (,) (getUPat upatl s) (getUPat upatr s')
getUPat (ULeft  upat) (Left s)  = getUPat upat s
getUPat (URight upat) (Right s) = getUPat upat s
getUPat (UChild  upat) s        = getUPat upat (out s)
getUPat (UElem upath upatt) []  = throwError $ ErrorInfo "UElem cannot accept empty source list"
getUPat (UElem upath upatt) (x: xs) = liftM2 (,) (getUPat upath x) (getUPat upatt xs)

getExpr :: MonadError' ErrorInfo m => Pat v v' c -> Expr v' v'' -> v'' -> m v'
getExpr pat expr v'' = undefined
--getExpr (EPath path)         v' = putbackPath path v' -- TODO:
--getExpr (EConst c )          v' = if v' == c then

-- v' is decided at the construction time when using constructor SubTree.
data SubTree v  where
  SubTree :: v' -> Path v v' -> SubTree v

getExprEnv :: MonadError' ErrorInfo m => Expr v v' -> v' -> m [SubTree v]
getExprEnv (EPath path)         v'          = return $ [ (SubTree v' path)]
getExprEnv (EConst c  )         v'          = if v' == c then return [] else (throwError $ ErrorInfo "v is not a constant")
getExprEnv (EChild expr)        v'          = getExprEnv expr (out v')
getExprEnv (EProd  exprl exprr) (vl', vr')  =
  catchBind (getExprEnv exprl vl')
            (\vls -> catchBind (getExprEnv exprr vr') (\vrs -> return (vls ++ vrs)) (\e -> throwError $ ErrorInfo "product right fail"))
            (\e -> throwError $ ErrorInfo "product left fail")
getExprEnv (ELeft expr)         (Left v')   = getExprEnv expr v'
getExprEnv (ELeft expr)         _           = throwError $ ErrorInfo "v' not match Either Left"
getExprEnv (ERight expr)        (Right v')  = getExprEnv expr v'
getExprEnv (ERight expr)        _           = throwError $ ErrorInfo "v' not match Either Right"
getExprEnv (EElem exprh exprt)  []          = throwError $ ErrorInfo "v' Elem cannot be empty"
getExprEnv (EElem exprh exprt)  (vh' : vt's)  =
  catchBind (getExprEnv exprh vh')
            (\vhs -> catchBind (getExprEnv exprt vt's) (\vts -> return (vhs ++ vts)) (\e -> throwError $ ErrorInfo "Expr Elem tail failed."))
            (\e -> throwError $ ErrorInfo "Expr Elem head failed" )






getCaseS :: MonadError' ErrorInfo m => [(s -> m Bool, CaseSBranch m s v)] -> s -> m v
getCaseS = undefined

getCaseV :: MonadError' ErrorInfo m => [CaseVBranch m s v] -> s -> m v
getCaseV = undefined

getAlign :: MonadError' ErrorInfo m =>
             (s -> m Bool)
          -> (s -> v -> m Bool)
          -> BiGUL m s v
          -> (v -> m s)
          -> (s -> m (Maybe s))
          -> [s]
          -> m [v]
getAlign = undefined
