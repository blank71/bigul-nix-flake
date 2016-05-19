-- | This module implements the rearrangement operations, which are based on pattern matching.

module Generics.BiGUL.PatternMatching where

import Generics.BiGUL
import Generics.BiGUL.Error

import GHC.InOut

import Control.Monad.Except


-- | Pattern matching: take a pattern and a value to which the pattern is applicable,
--   and deconstruct the value into components, collected in an environment.
--   An environment is a product of deconstructed components wrapped in 'Var',
--   and the structure of the product follows the pattern, as specified for the second index of 'Pat'.
--   For example:
--
--   >>> deconstruct ((PVar `PProd` PVar) `PProd` PRight PVar) ((0,1),Right 2)
--   Right ((Var 0,Var 1),Var 2)
deconstruct :: Pat a env con -> a -> Either (PatExprDirError a) env
deconstruct PVar          x         = return (Var x)
deconstruct PVar'         x         = return (Var x)
deconstruct (PConst c)    x         = if c == x then return () else throwError PEDConstantMismatch
deconstruct (l `PProd` r) (x, y)    = liftM2 (,) (liftE PEDProdLeft  (deconstruct l x))
                                                 (liftE PEDProdRight (deconstruct r y))
deconstruct (PLeft  p)    (Left  x) = liftE PEDEitherLeft  (deconstruct p x)
deconstruct p@(PLeft _)   _         = throwError PEDEitherMismatch
deconstruct (PRight p)    (Right x) = liftE PEDEitherRight (deconstruct p x)
deconstruct p@(PRight _)  _         = throwError PEDEitherMismatch
deconstruct (PIn p)       x         = liftE PEDIn (deconstruct p (out x))

-- | The inverse of 'deconstruct'. For example:
--
--   >>> construct ((PVar `PProd` PVar) `PProd` PRight PVar) ((Var 0,Var 1),Var 2)
--   ((0,1),Right 2)
--
--   Formally, we have
--
--   prop> deconstruct p x = Right env  ==>  construct p env = x
--   prop> deconstruct p (construct p env) = Right env
construct :: Pat a env con -> env -> a
construct PVar          (Var x) = x
construct PVar'         (Var x) = x
construct (PConst c)    _       = c
construct (l `PProd` r) (x, y)  = (construct l x, construct r y)
construct (PLeft  p)    x       = Left  (construct p x)
construct (PRight p)    x       = Right (construct p x)
construct (PIn p)       x       = inn (construct p x)

-- | Follow a direction into an environment and extract the component at the end. For example:
--
--   >>> retrieve (DLeft (DRight DVar)) ((Var 0,Var 1),Var 2)
--   1
retrieve :: Direction env a -> env -> a
retrieve  DVar      (Var x) = x
retrieve (DLeft  d) (x, _)  = retrieve d x
retrieve (DRight d) (_, y)  = retrieve d y

-- | Given an environment, compute the value of an expression. For example:
--
--   >>> eval (EDir (DRight DVar) `EProd` EDir (DLeft (DRight DVar)) `EProd` EDir (DLeft (DLeft DVar))) ((Var 0,Var 1),Var 2)
--   ((2,1),0)
eval :: Expr env a -> env -> a
eval (EDir d)      env = retrieve d env
eval (EConst c)    env = c
eval (l `EProd` r) env = (eval l env, eval r env)
eval (ELeft  e)    env = Left  (eval e env)
eval (ERight e)    env = Right (eval e env)
eval (EIn e)       env = inn (eval e env)

-- The goal is to update the "Maybe" con to fill in proper values.
-- con follow the structure of Pat
-- we have updated value a', which follows the structure of Expr
uneval :: Pat a env con -> Expr env b -> b -> con -> Either (PatExprDirError b) con
uneval p (EDir d)     x         con = unevalDir p d x con
uneval p (EConst c)   x         con = if c == x then return con else throwError PEDConstantMismatch
uneval p (EIn e)      x         con = liftE PEDIn (uneval p e (out x) con)
uneval p (EProd l r)  (x, y)    con = liftE PEDProdLeft (uneval p l x con) >>= liftE PEDProdRight . uneval p r y
uneval p (ELeft  e)   (Left  x) con = liftE PEDEitherLeft (uneval p e x con)
uneval p e@(ELeft _)  x         con = throwError PEDEitherMismatch
uneval p (ERight e)   (Right x) con = liftE PEDEitherRight (uneval p e x con)
uneval p e@(ERight _) x         con = throwError PEDEitherMismatch

unevalDir :: Pat a env con -> Direction env b -> b -> con -> Either (PatExprDirError b) con
unevalDir PVar          DVar       x (Just y)     = if x == y
                                                    then return (Just x)
                                                    else throwError (PEDIncompatibleUpdates x y)
unevalDir PVar          DVar       x Nothing      = return (Just x)
unevalDir PVar'         DVar       x (Just y)     = throwError (PEDMultipleUpdates x y)
unevalDir PVar'         DVar       x Nothing      = return (Just x)
unevalDir (PConst c)    _          x con          = return con
unevalDir (l `PProd` r) (DLeft  d) x (conl, conr) = liftM (, conr) (unevalDir l d x conl)
unevalDir (l `PProd` r) (DRight d) x (conl, conr) = liftM (conl ,) (unevalDir r d x conr)
unevalDir (PLeft  p)    d          x con          = unevalDir p d x con
unevalDir (PRight p)    d          x con          = unevalDir p d x con
unevalDir (PIn p)       d          x con          = unevalDir p d x con

fromContainerV :: Pat v env con -> con -> Either (PatExprDirError v) env
fromContainerV PVar              Nothing      = throwError PEDValueUnrecoverable
fromContainerV PVar              (Just v)     = return (Var v)
fromContainerV PVar'             Nothing      = throwError PEDValueUnrecoverable
fromContainerV PVar'             (Just v)     = return (Var v)
fromContainerV (PConst c)        con          = return ()
fromContainerV (PProd patl patr) (conl, conr) = liftM2 (,) (liftE PEDProdLeft  (fromContainerV patl conl))
                                                           (liftE PEDProdRight (fromContainerV patr conr))
fromContainerV (PLeft pat)       con          = liftE PEDEitherLeft  (fromContainerV pat con)
fromContainerV (PRight pat)      con          = liftE PEDEitherRight (fromContainerV pat con)
fromContainerV (PIn pat)         con          = liftE PEDIn (fromContainerV pat con)

fromContainerS :: Pat s env con -> env -> con -> env
fromContainerS PVar              (Var s)     Nothing     = (Var s)
fromContainerS PVar              (Var s)     (Just s')   = (Var s')
fromContainerS PVar'             (Var s)     Nothing     = (Var s)
fromContainerS PVar'             (Var s)     (Just s')   = (Var s')
fromContainerS (PConst c)        _           _           = ()
fromContainerS (PProd lpat rpat) (env, env') (con, con') = (fromContainerS lpat env con, fromContainerS rpat env' con')
fromContainerS (PLeft pat)       env         con         = fromContainerS pat env con
fromContainerS (PRight pat)      env         con         = fromContainerS pat env con
fromContainerS (PIn pat)         env         con         = fromContainerS pat env con

emptyContainer :: Pat v env con -> con
emptyContainer PVar                = Nothing
emptyContainer PVar'               = Nothing
emptyContainer (PConst  c)         = ()
emptyContainer (PProd rpatl rpatr) = (emptyContainer rpatl, emptyContainer rpatr)
emptyContainer (PLeft pat        ) = emptyContainer pat
emptyContainer (PRight pat       ) = emptyContainer pat
emptyContainer (PIn  pat         ) = emptyContainer pat

-- checkFullEmbedding :: BiGUL s v -> Either [String] ()
-- checkFullEmbedding (Fail _)        = return ()
-- checkFullEmbedding (Skip _)        = return ()
-- checkFullEmbedding  Replace        = return ()
-- checkFullEmbedding (l `Prod` r)    = checkFullEmbedding l && checkFullEmbedding
-- checkFullEmbedding (RearrS p e b)  = checkFullEmbedding b
-- checkFullEmbedding (RearrV p e b)  = check e p && checkFullEmbedding b
-- checkFullEmbedding (Dep f b)       = checkFullEmbedding bigul
-- checkFullEmbedding (Case bs)       = and (map (checkCaseBranch . snd) bs)
-- checkFullEmbedding (l `Compose` r) = checkFullEmbedding l && checkFullEmbedding r

-- checkCaseBranch :: CaseBranch s v -> Bool
-- checkCaseBranch (_, Normal b _) = checkFullEmbedding b
-- checkCaseBranch (_, Adaptive _) = True

-- checkRearr :: Expr env v' -> Pat v env con -> Bool
-- checkRearr expr pat = checkCon pat (abstractUpdateCon expr pat (emptyContainer pat))

-- abstractUpdateCon :: Expr env a' -> Pat a env con -> con -> con
-- abstractUpdateCon (EDir dir)          pat con = abstractUpdateDir pat dir con
-- abstractUpdateCon (EConst c)          pat con = con
-- abstractUpdateCon (EIn expr)          pat con = abstractUpdateCon expr pat con
-- abstractUpdateCon (EProd exprl exprr) pat con = abstractUpdateCon exprr pat (abstractUpdateCon exprl pat con)
-- abstractUpdateCon (ELeft expr)        pat con = abstractUpdateCon expr  pat con
-- abstractUpdateCon (ERight expr)       pat con = abstractUpdateCon expr  pat con

-- abstractUpdateDir :: Pat a env con -> Direction env a' -> con -> con
-- abstractUpdateDir PVar              DVar         Nothing      = Just undefined
-- abstractUpdateDir PVar              DVar         (Just _)     = Just undefined
-- abstractUpdateDir (PConst c)        _            con          = con
-- abstractUpdateDir (PProd patl patr) (DLeft dir)  (conl, conr) = (abstractUpdateDir patl dir conl, conr)
-- abstractUpdateDir (PProd patl patr) (DRight dir) (conl, conr) = (conl, abstractUpdateDir patr dir conr)
-- abstractUpdateDir (PLeft patl     ) dir          con          = abstractUpdateDir patl dir con
-- abstractUpdateDir (PRight patr    ) dir          con          = abstractUpdateDir patr dir con
-- abstractUpdateDir (PIn pat        ) dir          con          = abstractUpdateDir pat  dir con

-- checkCon :: Pat v env con -> con -> Bool
-- checkCon PVar               (Just _)     = True
-- checkCon PVar               Nothing      = False
-- checkCon (PConst c)         _            = True
-- checkCon (PProd patl patr)  (conl, conr) = checkCon patl conl && checkCon patr conr
-- checkCon (PLeft  patl)      con          = checkCon patl con
-- checkCon (PRight patr)      con          = checkCon patr con
-- -- checkCon (PIn pat    )      con          = checkCon pat  con
