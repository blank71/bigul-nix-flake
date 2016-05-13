module Generics.BiGUL.Interpreter (put, get, PutResult, GetResult, errorTrace) where

import Generics.BiGUL
import Generics.BiGUL.Error
import Generics.BiGUL.PatternMatching
import Control.Monad.Except
import Text.PrettyPrint


errorTrace :: PrettyPrintable e => Either e a -> Either Doc a
errorTrace = either (Left . (text "error" $+$) . toDoc) Right

catchBind :: Either e a -> (a -> Either e b) -> (e -> Either e b) -> Either e b
catchBind ma f g = either g f ma

type PutResult s v = Either (PutError s v) s

put :: BiGUL s v -> s -> v -> PutResult s v
put (Fail str)              s       v       = throwError (PFail str)
put (Skip f)                s       v       = if f s == v then return s else throwError PSkipMismatch
put Replace                 s       v       = return v
put (Prod bigul bigul')     (s, s') (v, v') = liftM2 (,) (liftE (PProdLeft  s  v ) (put bigul  s  v ))
                                                         (liftE (PProdRight s' v') (put bigul' s' v'))
put (RearrS pat expr bigul) s       v       = do env <- liftE PSourcePatternMismatch (deconstruct pat s)
                                                 let m = eval expr env
                                                 s'  <- liftE (PRearrS m v) (put bigul m v)
                                                 con <- liftE PUnevalFailed (uneval pat expr s' (emptyContainer pat))
                                                 return (construct pat (fromContainerS pat env con))
put (RearrV pat expr bigul) s       v       = do v' <- liftE PViewPatternMismatch (deconstruct pat v)
                                                 let m = eval expr v'
                                                 liftE (PRearrV s m) (put bigul s m)
put (Dep f b)               s       (v, v') = if f v == v' then liftE (PDep s v) (put b s v)
                                                          else throwError PDependencyMismatch
put (Case branches)         s       v       = putCase branches s v
put (Compose bigul bigul')  s       v       = do m  <- liftE PNoIntermediateSource (get bigul s)
                                                 m' <- liftE (PComposeRight m v) (put bigul' m v)
                                                 liftE (PComposeLeft s m') (put bigul s m')

getCaseBranch :: (s -> v -> Bool, CaseBranch s v) -> s -> GetResult s v
getCaseBranch (p , Normal bigul q) s =
  if q s
  then do v <- get bigul s
          if p s v
          then return v
          else throwError GPostVerificationFailed
  else throwError GBranchUnmatched
getCaseBranch (p , Adaptive f)     s = throwError GAdaptiveBranchMatched

putCaseCheckDiversion :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v -> Either (PutError s v) ()
putCaseCheckDiversion []             s v = return ()
putCaseCheckDiversion (pb@(p, b):bs) s v =
  if not (p s v)
  then catchBind (liftE (const undefined) (getCaseBranch pb s))
                 (const (throwError PPreviousBranchMatched))
                 (const (putCaseCheckDiversion bs s v))
  else throwError PPreviousBranchMatched

putCaseWithAdaptation :: [(s -> v -> Bool, CaseBranch s v)] -> [(s -> v -> Bool, CaseBranch s v)] ->
                         s -> v -> (s -> PutResult s v) -> PutResult s v
putCaseWithAdaptation []             bs' s v cont = throwError PCaseExhausted
putCaseWithAdaptation (pb@(p, b):bs) bs' s v cont =
  if p s v
  then liftE (PBranch 0) $
       case b of
         Normal bigul q -> do
           s' <- put bigul s v
           if p s' v
           then if q s'
                then putCaseCheckDiversion bs' s' v >> return s'
                else throwError PBranchPredictionIncorrect
           else throwError PPostVerificationFailed
         Adaptive f -> cont (f s v)
  else liftE incrBranchNo (putCaseWithAdaptation bs (pb:bs') s v cont)

putCase :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v -> Either (PutError s v) s
putCase bs s v = putCaseWithAdaptation bs [] s v
                   (\s' -> putCaseWithAdaptation bs [] s' v
                             (const (throwError PAdaptiveBranchRevisited)))

type GetResult s v = Either (GetError s v) v

get :: BiGUL s v -> s -> GetResult s v
get (Fail str)              s       = throwError (GFail str)
get (Skip f)                s       = return (f s)
get Replace                 s       = return s
get (Prod bigul bigul')     (s, s') = liftM2 (,) (liftE (GProdLeft  s ) (get bigul  s ))
                                                 (liftE (GProdRight s') (get bigul' s'))
get (RearrS pat expr bigul) s       = do env <- liftE GSourcePatternMismatch (deconstruct pat s)
                                         let m = eval expr env
                                         liftE (GRearrS m) (get bigul m)
get (RearrV pat expr bigul) s       = do v'  <- liftE (GRearrV s) (get bigul s)
                                         con <- liftE GUnevalFailed (uneval pat expr v' (emptyContainer pat))
                                         env <- liftE GViewRecoveringIncomplete (fromContainerV pat con)
                                         return (construct pat env)
get (Dep f b)               s       = do v <- liftE (GDep s) (get b s)
                                         return (v, f v)
get (Case branches)         s       = getCase branches s
get (Compose bigul bigul')  s       = do m <- liftE (GComposeLeft s) (get bigul s)
                                         liftE (GComposeRight m) (get bigul' m)

getCase :: [(s -> v -> Bool, CaseBranch s v)] -> s -> GetResult s v
getCase []             s = throwError (GCaseExhausted [])
getCase (pb@(p, b):bs) s =
  catchBind (getCaseBranch pb s) return
            (\e -> do v <- liftE (addCurrentBranchError e) (getCase bs s)
                      if not (p s v)
                      then return v
                      else throwError (GBranch 0 GPreviousBranchMatched))
