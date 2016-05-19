-- | This is the main module defining the syntax of BiGUL.
--   To execute BiGUL programs, use 'Generics.BiGUL.Interpreter.put' and 'Generics.BiGUL.Interpreter.get'
--   from "Generics.BiGUL.Interpreter".
--   See "Generics.BiGUL.Lib.HuStudies" for some small, illustrative examples.

module Generics.BiGUL(
  -- * Main syntax
    BiGUL(..)
  , CaseBranch(..)
  -- * Rearrangement syntax
  -- | The following pattern and expression syntax for rearrangement operations are designed to be type-safe
  --   but not intended to be programmer-friendly. The programmer is expected to use the higher-level syntax
  --   from "Generics.BiGUL.TH", which desugars into the following raw syntax.
  --   For more detail about patterns and expressions, see "Generics.BiGUL.PatternMatching".
  , Pat(..)
  , Var(..)
  , Direction(..)
  , Expr(..)) where


import GHC.InOut

import Control.Monad.State
import Text.PrettyPrint


-- | This is the datatype of BiGUL programs, as a GADT indexed with the source and view types.
--   Before the advent of GHC 8, haddock does not support documentation for GADT constructors;
--   for now, see the source for the description of each constructor and its arguments.
data BiGUL s v where

  -- Abort computation and emit an error message.
  Fail    :: String  -- error message
          -> BiGUL s v

  -- Keep the source unchanged, with the side condition that the view can be completely determined from the source.
  -- Use Generics.BiGUL.Lib.skip when the view is a constant.
  Skip    :: Eq v
          => (s -> v)  -- how the view can be computed from the source
          -> BiGUL s v

  -- Replace the source with the view (which should have the same type as the source).
  Replace :: BiGUL s s

  -- When the source and view are both pairs, perform update on the first/second source and view components
  -- using the first/second inner program.
  Prod    :: BiGUL s v    -- program for updating the first components
          -> BiGUL s' v'  -- program for updating the second components
          -> BiGUL (s, s') (v, v')

  -- Rearrange the source into an intermediate form, which is updated by the inner program,
  -- and then invert the rearrangement.
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
  Case    :: [(s -> v -> Bool, CaseBranch s v)]  -- branches, each of which consists of
                                                 -- a main condition (on both the source and view)
                                                 -- and an inner action
          -> BiGUL s v

  -- Standard composition of bidirectional transformations.
  Compose :: BiGUL s u
          -> BiGUL u v
          -> BiGUL s v

infixr 1 `Prod`
infixr 1 `Compose`

-- | A branch used in 'Case' (whose type is parametrised by the source and view types)
--   can be either 'Normal' or 'Adaptive'.
--   The exit conditions specified in 'Normal' branches should (ideally) be disjoint.
data CaseBranch s v =
    -- | A 'Normal' branch contains an inner program, which should update the source such that
    --   both the main condition (on both the source and view) and the exit condition (on the source) are satisfied.
    Normal (BiGUL s v) (s -> Bool)
    -- | An 'Adaptive' branch contains an adaptation function, which should modify the source such that
    --   a 'Normal' branch is applicable.
  | Adaptive (s -> v -> s)


-- | The datatype of patterns is indexed by three types: the type of values to which a pattern is applicable,
--   the type of environments resulting from pattern matching, and the type of containers used during
--   inverse evaluation of expressions.
data Pat a env con where

  -- Variable pattern, the value extracted from which can be duplicated.
  PVar   :: Eq a
         => Pat a (Var a) (Maybe a)

  -- Variable pattern, the value extracted from which cannot be duplicated.
  PVar'  :: Pat a (Var a) (Maybe a)

  -- Constant pattern.
  PConst :: (Eq a)
         => a  -- constant to be matched
         -> Pat a () ()

  -- Product pattern.
  PProd  :: Pat a a' a''  -- left-hand side pattern
         -> Pat b b' b''  -- right-hand side pattern
         -> Pat (a, b) (a', b') (a'', b'')

  -- Left pattern, matching values of shape `Left x :: Either a b` for some `x :: a`.
  PLeft  :: Pat a a' a''  -- inner pattern
         -> Pat (Either a b) a' a''

  -- Right pattern, matching values of shape `Right y :: Either a b` for some `y :: b`.
  PRight :: Pat b b' b''  -- inner pattern
         -> Pat (Either a b) b' b''

  -- Constructor pattern, unwrapping a value to its sum-of-products representation.
  -- (Invoke 'Generics.BiGUL.TH.deriveBiGULGenerics' on the datatype involved first.)
  PIn    :: InOut a
         => Pat (F a) b c  -- inner pattern
         -> Pat a b c

infixr 1 `PProd`

-- | A marker for variable positions in environment types.
newtype Var a = Var a deriving (Show, Eq)

-- | Directions point to a variable position (marked by 'Var') in an environment.
--   Their type is indexed by the environment type and the type of the variable position being pointed to.
data Direction env a where

  -- Point to the current variable position.
  DVar    :: Direction (Var a) a

  -- Point to the left part of the environment.
  DLeft   :: Direction a t
          -> Direction (a, b) t

  -- Point to the right part of the environment.
  DRight  :: Direction b t -> Direction (a, b) t

-- | Expressions are patterns whose variable positions contain directions pointing into some environment.
--   Their type is indexed by the environment type and the type of the expressed value.
data Expr env a where

  -- Direction expression, referring to a value in the environment.
  EDir   :: Direction env a
         -> Expr env a

  -- Constant expression.
  EConst :: Eq a
         => a  -- constant
         -> Expr env a

  -- Product expression.
  EProd  :: Expr env a  -- left-hand side expression
         -> Expr env b  -- right-hand side expression
         -> Expr env (a, b)

  -- Left expression (producing an 'Either'-value).
  ELeft  :: Expr env a
         -> Expr env (Either a b)

  -- Right expression (producing an 'Either'-value).
  ERight :: Expr env b
         -> Expr env (Either a b)

  -- Constructor expression, wrapping a sum-of-products representation into data.
  -- (Invoke 'Generics.BiGUL.TH.deriveBiGULGenerics' on the datatype involved first.)
  EIn    :: InOut a => Expr env (F a) -> Expr env a

infixr 1 `EProd`
