{-# LANGUAGE GADTs, KindSignatures, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveGeneric, TupleSections #-}
module Generics.BiGUL.Interpreter (put, get) where

import Generics.BiGUL.AST
import Control.Monad
import Control.Monad.Except
import GHC.InOut

catchBind :: Either e a -> (a -> Either e b) -> (e -> Either e b) -> Either e b
catchBind ma f g = either g f ma

data BiGULPutError :: * -> * -> * where
  BPFail                      :: String -> BiGULPutError s v
  BPSourcePatternMismatch     :: PatExprDirError s -> BiGULPutError s v
  BPViewPatternMismatch       :: PatExprDirError v -> BiGULPutError s v
  BPUnevalFailed              :: PatExprDirError s' -> BiGULPutError s v
  BPViewRecoveringIncomplete  :: PatExprDirError v' -> BiGULPutError s v
  BPDependencyMismatch        :: s -> BiGULPutError s (v, v')
  BPNoIntermediateSource      :: BiGULGetError s v' -> BiGULPutError s v
  BPCaseExhausted             :: BiGULPutError s v
  BPAdaptiveBranchRevisited   :: BiGULPutError s v
  BPAdaptiveBranchMatched     :: BiGULPutError s v
  BPPreviousBranchMatched     :: BiGULPutError s v
  BPBranchPredictionIncorrect :: BiGULPutError s v
  BPPostVerificationFailed    :: BiGULPutError s v
  BPBranchUnmatched           :: BiGULPutError s v
  --
  BPProdLeft     :: s -> v -> BiGULPutError s v -> BiGULPutError (s, s') (v, v')
  BPProdRight    :: s' -> v' -> BiGULPutError s' v' -> BiGULPutError (s, s') (v, v')
  BPRearrS       :: s' -> v -> BiGULPutError s' v -> BiGULPutError s v
  BPRearrV       :: s -> v' -> BiGULPutError s v' -> BiGULPutError s v
  BPDep          :: s -> v -> BiGULPutError s v -> BiGULPutError s (v, v')
  BPComposeLeft  :: a -> b -> BiGULPutError a b -> BiGULPutError a c
  BPComposeRight :: b -> c -> BiGULPutError b c -> BiGULPutError a c
  BPBranch       :: Int -> BiGULPutError s v -> BiGULPutError s v

incrBranchNo :: BiGULPutError s v -> BiGULPutError s v
incrBranchNo (BPBranch i e) = BPBranch (i+1) e
incrBranchNo e              = e

instance Show (BiGULPutError s v) where
  show (BPFail str)                   = "fail: " ++ str
  show (BPSourcePatternMismatch e)    = "source pattern mismatch\n" ++ show e
  show (BPViewPatternMismatch e)      = "view pattern mismatch\n" ++ show e
  show (BPUnevalFailed e)             = "uneval failed\n" ++ show e
  show (BPViewRecoveringIncomplete e) = "recovering incomplete\n" ++ show e
  show (BPDependencyMismatch _)       = "dependency mismatch"
  show (BPNoIntermediateSource e)     = "no intermediate source\n" ++ show e
  show  BPCaseExhausted               = "case exhausted"
  show  BPAdaptiveBranchRevisited     = "adaptive branch revisited"
  show  BPAdaptiveBranchMatched       = "adaptive branch matched"
  show  BPPreviousBranchMatched       = "previous branch matched"
  show  BPBranchPredictionIncorrect   = "branch prediction incorrect"
  show  BPPostVerificationFailed      = "post-verification failed"
  show  BPBranchUnmatched             = "branch unmatched"
  show (BPProdLeft _ _ e)             = "on the left-hand side of Prod\n" ++ show e
  show (BPProdRight _ _ e)            = "on the right-hand side of Prod\n" ++ show e
  show (BPRearrS _ _ e)               = "in RearrS\n" ++ show e
  show (BPRearrV _ _ e)               = "in RearrV\n" ++ show e
  show (BPDep _ _ e)                  = "in Dep\n" ++ show e
  show (BPComposeLeft _ _ e)          = "on the left-hand side of Compose\n" ++ show e
  show (BPComposeRight _ _ e)         = "on the right-hand side of Compose\n" ++ show e
  show (BPBranch i e)                 = "in branch " ++ show i ++ "\n" ++ show e

data BiGULGetError :: * -> * -> * where
  BGFail                      :: String -> BiGULGetError s v
  BGSourcePatternMismatch     :: PatExprDirError s -> BiGULGetError s v
  BGUnevalFailed              :: PatExprDirError s' -> BiGULGetError s v
  BGViewRecoveringIncomplete  :: PatExprDirError v' -> BiGULGetError s v
  BGCaseExhausted             :: [BiGULGetError s v] -> BiGULGetError s v
  BGPreviousBranchMatched     :: BiGULGetError s v
  BGPostVerificationFailed    :: BiGULGetError s v
  BGBranchUnmatched           :: BiGULGetError s v
  BGAdaptiveBranchMatched     :: BiGULGetError s v
  --
  BGProdLeft     :: s -> BiGULGetError s v -> BiGULGetError (s, s') (v, v')
  BGProdRight    :: s' -> BiGULGetError s' v' -> BiGULGetError (s, s') (v, v')
  BGRearrS       :: s' -> BiGULGetError s' v -> BiGULGetError s v
  BGRearrV       :: s -> BiGULGetError s v' -> BiGULGetError s v
  BGDep          :: s -> BiGULGetError s v -> BiGULGetError s (v, v')
  BGComposeLeft  :: a -> BiGULGetError a b -> BiGULGetError a c
  BGComposeRight :: b -> BiGULGetError b c -> BiGULGetError a c
  BGBranch       :: Int -> BiGULGetError s v -> BiGULGetError s v

addCurrentBranchError :: BiGULGetError s v -> BiGULGetError s v -> BiGULGetError s v
addCurrentBranchError e0 (BGCaseExhausted es) = BGCaseExhausted (e0:es)
addCurrentBranchError e0 (BGBranch i e) = BGBranch (i+1) e

unlines' :: [String] -> String
unlines' = init . unlines

indent :: String -> String
indent = unlines' . map ("  "++) . lines

instance Show (BiGULGetError s v) where
  show (BGFail str)                   = "fail: " ++ str
  show (BGSourcePatternMismatch e)    = "source pattern mismatch\n" ++ show e
  show (BGUnevalFailed e)             = "uneval failed\n" ++ show e
  show (BGViewRecoveringIncomplete e) = "recovering incomplete\n" ++ show e
  show (BGCaseExhausted es)           = "case exhausted:\n" ++
                                        indent (unlines' (map (\(i, e) -> "branch " ++ show i ++ ":\n" ++
                                                                          indent (show e)) (zip [0..] es)))
  show  BGAdaptiveBranchMatched       = "adaptive branch matched"
  show  BGPreviousBranchMatched       = "previous branch matched"
  show  BGPostVerificationFailed      = "post-verification failed"
  show  BGBranchUnmatched             = "branch unmatched"
  show (BGProdLeft _ e)               = "on the left-hand side of Prod\n" ++ show e
  show (BGProdRight _ e)              = "on the right-hand side of Prod\n" ++ show e
  show (BGRearrS _ e)                 = "in RearrS\n" ++ show e
  show (BGRearrV _ e)                 = "in RearrV\n" ++ show e
  show (BGDep _ e)                    = "in Dep\n" ++ show e
  show (BGComposeLeft _ e)            = "on the left-hand side of Compose\n" ++ show e
  show (BGComposeRight _ e)           = "on the right-hand side of Compose\n" ++ show e
  show (BGBranch i e)                 = "in branch " ++ show i ++ "\n" ++ show e

put :: BiGUL s v -> s -> v -> Either (BiGULPutError s v) s
put (Fail str)              s       v       = throwError (BPFail str)
put Skip                    s       v       = return s
put Replace                 s       v       = return v
put (Prod bigul bigul')     (s, s') (v, v') = liftM2 (,) (liftE (BPProdLeft  s  v ) (put bigul  s  v ))
                                                         (liftE (BPProdRight s' v') (put bigul' s' v'))
put (RearrS pat expr bigul) s       v       = do env <- liftE BPSourcePatternMismatch (deconstruct pat s)
                                                 let m = eval expr env
                                                 s'  <- liftE (BPRearrS m v) (put bigul m v)
                                                 con <- liftE BPUnevalFailed (uneval pat expr s' (emptyContainer pat))
                                                 return (construct pat (fromContainerS pat env con))
put (RearrV pat expr bigul) s       v       = do v' <- liftE BPViewPatternMismatch (deconstruct pat v)
                                                 let m = eval expr v'
                                                 liftE (BPRearrV s m) (put bigul s m)
put (Dep bigul f)           s       (v, v') = do s' <- liftE (BPDep s v) (put bigul s v)
                                                 if f s' v == v'
                                                 then return s'
                                                 else throwError (BPDependencyMismatch s')
put (Case branches)         s       v       = putCase branches s v
put (Compose bigul bigul')  s       v       = do m  <- liftE BPNoIntermediateSource (get bigul s)
                                                 m' <- liftE (BPComposeRight m v) (put bigul' m v)
                                                 liftE (BPComposeLeft s m') (put bigul s m')

getCaseBranch :: (s -> v -> Bool, CaseBranch s v) -> s -> Either (BiGULGetError s v) v
getCaseBranch (p , Normal bigul q) s =
  if q s
  then do v <- get bigul s
          if p s v
          then return v
          else throwError BGPostVerificationFailed
  else throwError BGBranchUnmatched
getCaseBranch (p , Adaptive f)     s = throwError BGAdaptiveBranchMatched

putCaseCheckDiversion :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v -> Either (BiGULPutError s v) ()
putCaseCheckDiversion []             s v = return ()
putCaseCheckDiversion (pb@(p, b):bs) s v =
  if not (p s v)
  then catchBind (liftE (const undefined) (getCaseBranch pb s))
                 (const (throwError BPPreviousBranchMatched))
                 (const (putCaseCheckDiversion bs s v))
  else throwError BPPreviousBranchMatched

putCaseWithAdaptation :: [(s -> v -> Bool, CaseBranch s v)] -> [(s -> v -> Bool, CaseBranch s v)] ->
                         s -> v -> (s -> Either (BiGULPutError s v) s) -> Either (BiGULPutError s v) s
putCaseWithAdaptation []             bs' s v cont = throwError BPCaseExhausted
putCaseWithAdaptation (pb@(p, b):bs) bs' s v cont =
  if p s v
  then liftE (BPBranch 0) $
       case b of
         Normal bigul q -> do
           s' <- put bigul s v
           if p s' v
           then if q s'
                then putCaseCheckDiversion bs' s' v >> return s'
                else throwError BPBranchPredictionIncorrect
           else throwError BPPostVerificationFailed
         Adaptive f -> cont (f s v)
  else liftE incrBranchNo (putCaseWithAdaptation bs (pb:bs') s v cont)

putCase :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v -> Either (BiGULPutError s v) s
putCase bs s v = putCaseWithAdaptation bs [] s v
                   (\s' -> putCaseWithAdaptation bs [] s' v
                             (const (throwError BPAdaptiveBranchRevisited)))

get :: BiGUL s v -> s -> Either (BiGULGetError s v) v
get (Fail str)              s       = throwError (BGFail str)
get Skip                    s       = return ()
get Replace                 s       = return s
get (Prod bigul bigul')     (s, s') = liftM2 (,) (liftE (BGProdLeft  s ) (get bigul  s ))
                                                 (liftE (BGProdRight s') (get bigul' s'))
get (RearrS pat expr bigul) s       = do env <- liftE BGSourcePatternMismatch (deconstruct pat s)
                                         let m = eval expr env
                                         liftE (BGRearrS m) (get bigul m)
get (RearrV pat expr bigul) s       = do v'  <- liftE (BGRearrV s) (get bigul s)
                                         con <- liftE BGUnevalFailed (uneval pat expr v' (emptyContainer pat))
                                         env <- liftE BGViewRecoveringIncomplete (fromContainerV pat con)
                                         return (construct pat env)
get (Dep bigul f)           s       = do v <- liftE (BGDep s) (get bigul s)
                                         return (v, f s v)
get (Case branches)         s       = getCase branches s
get (Compose bigul bigul')  s       = do m <- liftE (BGComposeLeft s) (get bigul s)
                                         liftE (BGComposeRight m) (get bigul' m)

getCase :: [(s -> v -> Bool, CaseBranch s v)] -> s -> Either (BiGULGetError s v) v
getCase []             s = throwError (BGCaseExhausted [])
getCase (pb@(p, b):bs) s =
  catchBind (getCaseBranch pb s) return
            (\e -> do v <- liftE (addCurrentBranchError e) (getCase bs s)
                      if not (p s v)
                      then return v
                      else throwError (BGBranch 0 BGPreviousBranchMatched))
