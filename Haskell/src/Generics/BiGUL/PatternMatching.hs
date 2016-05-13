module Generics.BiGUL.PatternMatching where

import Generics.BiGUL
import Generics.BiGUL.Error

import GHC.InOut

import Control.Monad.Except


deconstruct :: Pat a env con -> a -> Either (PatExprDirError a) env
deconstruct PVar              a          = return (Var a)
deconstruct PVar'             a          = return (Var a)
deconstruct (PConst c)        a          = if c == a then return () else throwError PEDConstantMismatch
deconstruct (PProd patl patr) (al, ar)   = liftM2 (,) (liftE PEDProdLeft  (deconstruct patl al))
                                                      (liftE PEDProdRight (deconstruct patr ar))
deconstruct (PLeft patl)      (Left  al) = liftE PEDEitherLeft  (deconstruct patl al)
deconstruct pat@(PLeft _)     a          = throwError PEDEitherMismatch
deconstruct (PRight patr)     (Right ar) = liftE PEDEitherRight (deconstruct patr ar)
deconstruct pat@(PRight _)    a          = throwError PEDEitherMismatch
deconstruct (PIn pat)         a          = liftE PEDIn (deconstruct pat (out a))

construct :: Pat a env con -> env -> a
construct PVar              (Var a)  = a
construct PVar'             (Var a)  = a
construct (PConst c)        _        = c
construct (PProd patl patr) (al, ar) = (construct patl al, construct patr ar)
construct (PLeft patl)      al       = Left  (construct patl al)
construct (PRight patr)     ar       = Right (construct patr ar)
construct (PIn pat)         a        = inn (construct pat a)

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

retrieve :: Direction a t -> a -> t
retrieve  DVar      (Var x) = x
retrieve (DLeft  p) (x, y)  = retrieve p x
retrieve (DRight p) (x, y)  = retrieve p y

eval :: Expr env a' -> env -> a'
eval (EDir dir)          env = retrieve dir env
eval (EConst c)          env = c
eval (EIn expr)          env = inn (eval expr env)
eval (EProd exprl exprr) env = (eval exprl env, eval exprr env)
eval (ELeft expr       ) env = Left $ eval expr env
eval (ERight expr      ) env = Right $ eval expr env

-- The goal is to update the "Maybe" con to fill in proper values.
-- con follow the structure of Pat
-- we have updated value a', which follows the structure of Expr
uneval :: Pat a env con -> Expr env a' -> a' -> con -> Either (PatExprDirError a') con
uneval pat (EDir dir)          a'          con = unevalDir pat dir a' con
uneval pat (EConst c)          a'          con = if c == a' then return con else throwError PEDConstantMismatch
uneval pat (EIn expr)          a'          con = liftE PEDIn (uneval pat expr (out a') con)
uneval pat (EProd exprl exprr) (al', ar')  con = liftE PEDProdLeft (uneval pat exprl al' con) >>= liftE PEDProdRight . uneval pat exprr ar'
uneval pat (ELeft expr)        (Left al')  con = liftE PEDEitherLeft (uneval pat expr al' con)
uneval pat expr@(ELeft _)      a'          con = throwError PEDEitherMismatch
uneval pat (ERight expr)       (Right ar') con = liftE PEDEitherRight (uneval pat expr ar' con)
uneval pat expr@(ERight _)     a'          con = throwError PEDEitherMismatch

unevalDir :: Pat a env con -> Direction env a' -> a' -> con -> Either (PatExprDirError a') con
unevalDir PVar              DVar          a' (Just a'')   = if a' == a''
                                                            then return (Just a')
                                                            else throwError (PEDIncompatibleUpdates a' a'')
unevalDir PVar              DVar          a' Nothing      = return (Just a')
unevalDir PVar'             DVar          a' (Just a'')   = throwError (PEDMultipleUpdates a' a'')
unevalDir PVar'             DVar          a' Nothing      = return (Just a')
unevalDir (PConst c)        _             a' con          = return con
unevalDir (PProd patl patr) (DLeft dir)   a' (conl, conr) = liftM (, conr) (unevalDir patl dir a' conl)
unevalDir (PProd patl patr) (DRight dir)  a' (conl, conr) = liftM (conl ,) (unevalDir patr dir a' conr)
unevalDir (PLeft  patl    ) dir           a' con          = unevalDir patl dir a' con
unevalDir (PRight patr    ) dir           a' con          = unevalDir patr dir a' con
unevalDir (PIn pat        ) dir           a' con          = unevalDir pat  dir a' con

