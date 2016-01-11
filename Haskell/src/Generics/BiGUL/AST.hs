{-# LANGUAGE GADTs, KindSignatures, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveGeneric, TupleSections #-}
module Generics.BiGUL.AST where

import Control.Monad.Except
import GHC.Generics
import GHC.InOut
import Text.PrettyPrint
import Data.List(intersperse)


data CaseBranch s v = Normal (BiGUL s v) (s -> Bool) | Adaptive (s -> v -> s)

instance Show (CaseBranch s v) where
  show (Normal bigul _) = "Normal " ++ show bigul
  show (Adaptive _    ) = "Adaptive <adaptive function>"

data BiGUL :: * -> * -> * where
  Fail    :: String -> BiGUL s v
  Skip    :: BiGUL s ()
  Replace :: BiGUL s s
  Prod    :: BiGUL s v -> BiGUL s' v' -> BiGUL (s, s') (v, v')
  RearrS  :: Pat s env con -> Expr env s' -> BiGUL s' v -> BiGUL s v
  RearrV  :: Pat v env con -> Expr env v' -> BiGUL s v' -> BiGUL s v
  Dep     :: (Eq v') => BiGUL s v -> (s -> v -> v') -> BiGUL s (v, v')
  Case    :: [(s -> v -> Bool, CaseBranch s v)] -> BiGUL s v
  Compose :: BiGUL s u -> BiGUL u v -> BiGUL s v

instance Show (BiGUL s v) where
  show (Fail s) = "Fail: " ++ s
  show Skip = "Skip"
  show Replace = "Replace"
  show (Dep bigul _) = "(Dep   <dependency function>  " ++ show bigul ++ " )"
  show (Case bs) = "(Case [" ++ unwords (intersperse "\n" (map (\(_,b) -> "(predicate , " ++ show b ++ " )") bs)) ++ " ])"
  show _ = "Unknown BiGUL program in show"

newtype Var a = Var a

instance Show a => Show (Var a) where
  show (Var a) = "Var: " ++ show a

-- Pat (view type) (environment type) (container type)
data Pat :: * -> * -> * -> * where
  PVar   :: Eq a => Pat a (Var a) (Maybe a)
  PVar'  :: Pat a (Var a) (Maybe a)
  PConst :: (Eq a, Show a) => a -> Pat a () ()
  PProd  :: Pat a a' a'' -> Pat b b' b'' -> Pat (a, b) (a', b') (a'', b'')
  PLeft  :: Pat a a' a'' -> Pat (Either a b) a' a''
  PRight :: Pat b b' b'' -> Pat (Either a b) b' b''
  PIn    :: InOut a => Pat (F a) b c -> Pat a b c

instance Show (Pat v e c) where
  show  PVar           = "PVar"
  show  PVar'          = "PVar'"
  show (PConst c)      = show c
  show (PProd rp1 rp2) = "(PProd " ++ show rp1 ++ " " ++ show rp2 ++ " )"
  show (PLeft rp)      = "(PLeft " ++ show rp ++ " )"
  show (PRight rp)     = "(PRight " ++ show rp ++ " )"
  show (PIn rp)        = "(PIn " ++ show rp ++ " )"
  -- show _               = "show error in Pat"

data PatExprDirError :: * -> * where
  PEDConstantMismatch    :: a -> a -> PatExprDirError a
  PEDPatEitherMismatch   :: Pat (Either a b) env con -> Either a b -> PatExprDirError (Either a b)
  PEDExprEitherMismatch  :: Expr env (Either a b) -> Either a b -> PatExprDirError (Either a b)
  PEDValueUnrecoverable  :: PatExprDirError a
  PEDIncompatibleUpdates :: a -> a -> PatExprDirError a
  PEDMultipleUpdates     :: a -> a -> PatExprDirError a
  --
  PEDProdLeft    :: PatExprDirError a -> PatExprDirError (a, b)
  PEDProdRight   :: PatExprDirError b -> PatExprDirError (a, b)
  PEDEitherLeft  :: PatExprDirError a -> PatExprDirError (Either a b)
  PEDEitherRight :: PatExprDirError b -> PatExprDirError (Either a b)
  PEDIn          :: InOut a => PatExprDirError (F a) -> PatExprDirError a

instance Show (PatExprDirError a) where
  show (PEDConstantMismatch _ _)    = "constant mismatch"
  show (PEDPatEitherMismatch _ _)   = "either pattern mismatch"
  show (PEDExprEitherMismatch _ _)  = "either expression mismatch"
  show  PEDValueUnrecoverable       = "value unrecoverable"
  show (PEDIncompatibleUpdates _ _) = "incompatible updates"
  show (PEDMultipleUpdates _ _)     = "multiple updates"
  show (PEDProdLeft e)              = "on the left-hand side of Prod\n" ++ show e
  show (PEDProdRight e)             = "on the right-hand side of Prod\n" ++ show e
  show (PEDEitherLeft e)            = "inside Left\n" ++ show e
  show (PEDEitherRight e)           = "inside Right\n" ++ show e
  show (PEDIn e)                    = "inside In" ++ show e

liftE :: (a -> b) -> Either a c -> Either b c
liftE f = either (Left . f) Right

class LiftPED a b where
  liftPED' :: PatExprDirError a -> PatExprDirError b
  liftPED  :: Either (PatExprDirError a) c -> Either (PatExprDirError b) c
  liftPED  = liftE liftPED'

instance LiftPED a (a, b) where
  liftPED' = PEDProdLeft

instance LiftPED b (a, b) where
  liftPED' = PEDProdRight

instance LiftPED a (Either a b) where
  liftPED' = PEDEitherLeft

instance LiftPED b (Either a b) where
  liftPED' = PEDEitherRight

deconstruct :: Pat a env con -> a -> Either (PatExprDirError a) env
deconstruct PVar              a          = return (Var a)
deconstruct PVar'             a          = return (Var a)
deconstruct (PConst c)        a          = if c == a then return () else throwError (PEDConstantMismatch c a)
deconstruct (PProd patl patr) (al, ar)   = liftM2 (,) (liftPED (deconstruct patl al))
                                                      (liftPED (deconstruct patr ar))
deconstruct (PLeft patl)      (Left  al) = liftPED (deconstruct patl al)
deconstruct pat@(PLeft _)     a          = throwError (PEDPatEitherMismatch pat a)
deconstruct (PRight patr)     (Right ar) = liftPED (deconstruct patr ar)
deconstruct pat@(PRight _)    a          = throwError (PEDPatEitherMismatch pat a)
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
fromContainerV (PProd patl patr) (conl, conr) = liftM2 (,) (liftPED (fromContainerV patl conl))
                                                           (liftPED (fromContainerV patr conr))
fromContainerV (PLeft pat)       con          = liftPED (fromContainerV pat con)
fromContainerV (PRight pat)      con          = liftPED (fromContainerV pat con)
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

-- You need to explicitly specify the type arguments at the type level when using the Direction type.
-- From type, you could know the type of the data you want.
-- !comment: DMaybe did not used.
data Direction :: * -> * -> * where
  DVar    :: Direction (Var a) a
  DLeft   :: Direction a t -> Direction (a, b) t
  DRight  :: Direction b t -> Direction (a, b) t

instance Show (Direction a t) where
  show  DVar = "DVar"
  show (DLeft dir)  = "(DLeft " ++ show dir ++ " )"
  show (DRight dir) = "(DRight " ++ show dir ++ " )"

retrieve :: Direction a t -> a -> t
retrieve  DVar      (Var x) = x
retrieve (DLeft  p) (x, y)  = retrieve p x
retrieve (DRight p) (x, y)  = retrieve p y

data Expr :: * -> * -> * where
  EDir     :: Direction orig a -> Expr orig a
  EConst   :: (Eq a, Show a) =>  a -> Expr orig a
  EIn      :: (InOut a, Eq (F a)) => Expr orig (F a) -> Expr orig a
  EProd    :: Expr orig a -> Expr orig b -> Expr orig (a, b)
  ELeft    :: Expr orig a -> Expr orig (Either a b)
  ERight   :: Expr orig b -> Expr orig (Either a b)

instance Show (Expr orig a) where
  show (EDir dir)      = "(EDir " ++ show dir ++ " )"
  show (EConst c)      = "(EConst " ++ show c ++ " )"
  show (EProd e1 e2)   = "(EProd " ++ show e1 ++ " " ++ show e2 ++ " )"
  show (ELeft e)       = "(ELeft " ++ show e ++ " )"
  show (ERight e)      = "(ERight " ++ show e ++ " )"
  show (EIn e)         = "(EIn " ++ show e ++ " )"

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
uneval pat (EConst c)          a'          con = if c == a' then return con else throwError (PEDConstantMismatch c a')
uneval pat (EIn expr)          a'          con = liftE PEDIn (uneval pat expr (out a') con)
uneval pat (EProd exprl exprr) (al', ar')  con = liftPED (uneval pat exprl al' con) >>= liftPED . uneval pat exprr ar'
uneval pat (ELeft expr)        (Left al')  con = liftPED (uneval pat expr al' con)
uneval pat expr@(ELeft _)      a'          con = throwError (PEDExprEitherMismatch expr a')
uneval pat (ERight expr)       (Right ar') con = liftPED (uneval pat expr ar' con)
uneval pat expr@(ERight _)     a'          con = throwError (PEDExprEitherMismatch expr a')

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

-- TODO: static check of full embedding
-- checkFullEmbed :: BiGUL m s v -> Bool
-- checkFullEmbed Fail                    = True
-- checkFullEmbed Skip                    = True
-- checkFullEmbed Replace                 = True
-- checkFullEmbed (RearrS pat expr bigul) = checkFullEmbed bigul
-- checkFullEmbed (RearrV pat expr bigul) = checkRearr expr pat && checkFullEmbed bigul
-- checkFullEmbed (Dep bigul f)           = checkFullEmbed bigul
-- checkFullEmbed (Case branches)         = and (map checkBranch branches)

-- checkBranch :: (s -> v -> Bool, CaseBranch m s v)  -> Bool
-- checkBranch (cond, Normal bigul _) = checkFullEmbed bigul
-- checkBranch (cond, _)              = True

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
-- checkCon (PIn pat    )      con          = checkCon pat  con
