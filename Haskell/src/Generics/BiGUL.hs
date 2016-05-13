-- | This is the main module defining the syntax of BiGUL.
--   To execute BiGUL programs, use 'Generics.BiGUL.Interpreter.put' and 'Generics.BiGUL.Interpreter.get'
--   from "Generics.BiGUL.Interpreter".
--   For a more detailed introduction to programming in BiGUL, see "Generics.BiGUL.Lib.Tutorial".

module Generics.BiGUL where

import GHC.InOut

import Text.PrettyPrint


-- | This is the datatype of BiGUL programs, as a GADT indexed with the source and view types.
--   Before the advent of GHC 8, haddock does not support documentation for GADT constructors;
--   for now, see the source for the description of each constructor and its arguments.
data BiGUL :: * -> * -> * where

  -- Abort computation and emit an error message.
  Fail    :: String  -- error message
          -> BiGUL s v

  -- Keep the source unchanged, with the side condition that the view can be completely determined from the source.
  -- Use Generics.BiGUL.Lib.skip when the view is a constant.
  Skip    :: Eq v
          => (s -> v)  -- how the view can be computed from the source
          -> BiGUL s v

  -- Replace the source with the view (which is required to have the same type as the source).
  Replace :: BiGUL s s

  -- When the source and view are both pairs, perform update on the first/second source and view components
  -- using the first/second inner program.
  Prod    :: BiGUL s v    -- program for updating the first components
          -> BiGUL s' v'  -- program for updating the second components
          -> BiGUL (s, s') (v, v')

  -- Rearrange the source into an intermediate form, which is updated by the inner program,
  -- and then revert the rearrangement.
  -- /The inner program should make sure that the updated source still retains the intermediate form
  -- (so the reversion can succeed)./
  RearrS  :: Pat s env con  -- pattern for the original source
          -> Expr env s'    -- expression computing the intermediate source
          -> BiGUL s' v     -- program for updating the intermediate source
          -> BiGUL s v

  -- Rearrange the view into a new one before continuing with the remaining program.
  RearrV  :: Pat v env con  -- pattern for the original view
          -> Expr env v'    -- expression computing the new view
          -> BiGUL s v'     -- remaining program
          -> BiGUL s v

  -- When the view is a pair and the second component depends entirely on the first one,
  -- discard the second component and continue with the remaining program.
  Dep     :: Eq v'
          => (v -> v')  -- how the second component of the view can be computed from the first
          -> BiGUL s v  -- remaining program
          -> BiGUL s (v, v')

  -- Case analysis on both the source and view.
  Case    :: [(s -> v -> Bool, CaseBranch s v)]
          -> BiGUL s v

  -- Standard composition of bidirectional transformations.
  Compose :: BiGUL s u
          -> BiGUL u v
          -> BiGUL s v

infixr 1 `Prod`

instance Show (BiGUL s v) where
  show (Fail s)  = "Fail: " ++ s
  show (Skip _)  = "Skip <dependency function>"
  show Replace   = "Replace"
  show (Dep _ b) = "(Dep <dependency function> " ++ show b ++ ")"
  -- show (Case bs) = "(Case [" ++ unwords (intersperse "\n" (map (\(_,b) -> "(predicate, " ++ show b ++ ")") bs)) ++ " ])"
  show _         = "Unknown BiGUL program in show"

data CaseBranch s v = Normal (BiGUL s v) (s -> Bool)
                    | Adaptive (s -> v -> s)

instance Show (CaseBranch s v) where
  show (Normal bigul _) = "Normal " ++ show bigul
  show (Adaptive _    ) = "Adaptive <function>"

newtype Var a = Var a

instance Show a => Show (Var a) where
  show (Var a) = "Var: " ++ show a

-- Pat (view type) (environment type) (container type)
data Pat :: * -> * -> * -> * where
  PVar   :: Eq a => Pat a (Var a) (Maybe a)
  PVar'  :: Pat a (Var a) (Maybe a)
  PConst :: (Eq a) => a -> Pat a () ()
  PProd  :: Pat a a' a'' -> Pat b b' b'' -> Pat (a, b) (a', b') (a'', b'')
  PLeft  :: Pat a a' a'' -> Pat (Either a b) a' a''
  PRight :: Pat b b' b'' -> Pat (Either a b) b' b''
  PIn    :: InOut a => Pat (F a) b c -> Pat a b c

instance Show (Pat v e c) where
  show  PVar           = "PVar"
  show  PVar'          = "PVar'"
  show (PConst c)      = "PConst"
  show (PProd rp1 rp2) = "(PProd " ++ show rp1 ++ " " ++ show rp2 ++ ")"
  show (PLeft rp)      = "(PLeft " ++ show rp ++ ")"
  show (PRight rp)     = "(PRight " ++ show rp ++ ")"
  show (PIn rp)        = "(PIn " ++ show rp ++ ")"
  -- show _               = "show error in Pat"

-- You need to explicitly specify the type arguments at the type level when using the Direction type.
-- From type, you could know the type of the data you want.
-- !comment: DMaybe did not used.
data Direction :: * -> * -> * where
  DVar    :: Direction (Var a) a
  DLeft   :: Direction a t -> Direction (a, b) t
  DRight  :: Direction b t -> Direction (a, b) t

instance Show (Direction a t) where
  show  DVar = "DVar"
  show (DLeft dir)  = "(DLeft " ++ show dir ++ ")"
  show (DRight dir) = "(DRight " ++ show dir ++ ")"

data Expr :: * -> * -> * where
  EDir   :: Direction orig a -> Expr orig a
  EConst :: Eq a =>  a -> Expr orig a
  EIn    :: InOut a => Expr orig (F a) -> Expr orig a
  EProd  :: Expr orig a -> Expr orig b -> Expr orig (a, b)
  ELeft  :: Expr orig a -> Expr orig (Either a b)
  ERight :: Expr orig b -> Expr orig (Either a b)

instance Show (Expr orig a) where
  show (EDir dir)      = "(EDir " ++ show dir ++ ")"
  show (EConst c)      = "EConst"
  show (EProd e1 e2)   = "(EProd " ++ show e1 ++ " " ++ show e2 ++ ")"
  show (ELeft e)       = "(ELeft " ++ show e ++ ")"
  show (ERight e)      = "(ERight " ++ show e ++ ")"
  show (EIn e)         = "(EIn " ++ show e ++ ")"

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
