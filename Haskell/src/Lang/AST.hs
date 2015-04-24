{-# LANGUAGE GADTs, KindSignatures, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveGeneric #-}
module Lang.AST where

import Control.Monad.Except
import GHC.Generics
import GHC.InOut

class MonadError e m => MonadError' e m where
  catchBind :: m a -> (a -> m b) -> (e -> m b) -> m b

instance MonadError' e (Either e) where
  -- catchBind :: Either e a -> (a -> Either e b) -> (e -> Either e b) -> Either e b
  catchBind ma f g = either g f ma

data ErrorInfo = ErrorInfo String

data Pat :: * -> * -> * where
  PVar   :: Pat a a
  PConst :: Eq a => a -> Pat a ()
  PProd  :: Pat a a' -> Pat b b' -> Pat (a, b) (a', b')
  PLeft  :: Pat a a' -> Pat (Either a b) a'
  PRight :: Pat b b' -> Pat (Either a b) b'
  PChild :: InOut a => Pat (F a) b -> Pat a b
  PElem  :: Pat a b -> Pat [a] b' -> Pat [a] (b, b')

deconstruct :: MonadError' ErrorInfo m => Pat a b -> a -> m b
deconstruct  PVar             x         = return x
deconstruct (PConst y)        x         = if x == y then return () else throwError $ ErrorInfo "unmatched constant pattern"
deconstruct (PProd lpat rpat) (x, y)    = liftM2 (,) (deconstruct lpat x) (deconstruct rpat y)
deconstruct (PLeft  pat)      (Left  x) = deconstruct pat x
deconstruct (PLeft  pat)      (Right y) = throwError $ ErrorInfo  "left pattern for right value"
deconstruct (PRight pat)      (Left  x) = throwError $ ErrorInfo "right pattern for left value"
deconstruct (PRight pat)      (Right y) = deconstruct pat y
deconstruct (PChild pat)      x         = deconstruct pat (out x)
deconstruct (PElem hpat tpat) []        = throwError $ ErrorInfo "head-tail pattern for empty list"
deconstruct (PElem hpat tpat) (x : xs)  = liftM2 (,) (deconstruct hpat x) (deconstruct tpat xs)

construct :: Pat a b -> b -> a
construct  PVar             x      = x
construct (PConst y)        _      = y
construct (PProd lpat rpat) (x, y) = (construct lpat x, construct rpat y)
construct (PLeft  pat)      x      = Left  (construct pat x)
construct (PRight pat)      y      = Right (construct pat y)
construct (PChild pat)      x      = inn (construct pat x)
construct (PElem hpat tpat) (x, y) = construct hpat x : construct tpat y

data UPat :: (* -> *) -> * -> * -> * where
  UVar   :: BiGUL m s v -> UPat m s v
  UConst :: Eq s => s -> UPat m s ()
  UProd  :: UPat m s v -> UPat m s' v' -> UPat m (s, s') (v, v')
  ULeft  :: UPat m s v -> UPat m (Either s s') v
  URight :: UPat m s' v -> UPat m (Either s s') v
  UChild :: InOut s => UPat m (F s) v -> UPat m s v
  UElem  :: UPat m s v -> UPat m [s] v' -> UPat m [s] (v, v')

data CaseSBranch m s v = Normal (BiGUL m s v) | Adaptive (s -> m s)

data CaseVBranch m s v where
  CaseVBranch :: Pat v v' -> BiGUL m s v' -> CaseVBranch m s v

data BiGUL :: (* -> *) -> * -> * -> * where
  Fail    :: BiGUL m s v
  Skip    :: BiGUL m s ()
  Replace :: BiGUL m s s
  Update  :: UPat m s v -> BiGUL m s v
  Rearr   :: Expr v v' -> BiGUL m s v' -> BiGUL m s v
  Dep     :: (Eq v') => (v -> v') -> BiGUL m s v -> BiGUL m s (v, v')
  CaseS   :: [(s -> m Bool, CaseSBranch m s v)] -> BiGUL m s v
  CaseV   :: [CaseVBranch m s v] -> BiGUL m s v
  Align   :: (s -> m Bool)
          -> (s -> v -> m Bool)
          -> BiGUL m s v
          -> (v -> m s)
          -> (s -> m (Maybe s))
          -> BiGUL m [s] [v]

data Path :: * -> * -> * where
  STip   :: Path a a
  SChild :: InOut a => Path (F a) t -> Path a t
  SProdL :: Path a t -> Path (a, b) t
  SProdR :: Path b t -> Path (a, b) t
  SLeft  :: Path a t -> Path (Either a b) t
  SRight :: Path b t -> Path (Either a b) t
  SElemH :: Path  a  t -> Path [a] t
  SElemT :: Path [a] t -> Path [a] t

retrieve :: MonadError' ErrorInfo m => Path a t -> a -> m t
retrieve  STip      x         = return x
retrieve (SChild p) x         = retrieve p (out x)
retrieve (SProdL p) (x, y)    = retrieve p x
retrieve (SProdR p) (x, y)    = retrieve p y
retrieve (SLeft  p) (Left  x) = retrieve p x
retrieve (SLeft  p) (Right y) = throwError $ ErrorInfo "left path for right value"
retrieve (SRight p) (Left  x) = throwError $ ErrorInfo "right path for left value"
retrieve (SRight p) (Right y) = retrieve p y
retrieve (SElemH p) []        = throwError $ ErrorInfo "head path for empty list"
retrieve (SElemH p) (x : xs)  = retrieve p x
retrieve (SElemT p) []        = throwError $ ErrorInfo "tail path for empty list"
retrieve (SElemT p) (x : xs)  = retrieve p xs

data Expr :: * -> * -> * where
  EPath  :: Path orig a -> Expr orig a
  EConst :: a -> Expr orig a
  EChild :: InOut a => Expr orig (F a) -> Expr orig a
  EProd  :: Expr orig a -> Expr orig b -> Expr orig (a, b)
  ELeft  :: Expr orig a -> Expr orig (Either a b)
  ERight :: Expr orig b -> Expr orig (Either a b)
  EElem  :: Expr orig a -> Expr orig [a] -> Expr orig [a]

data SBook = SBook String [String] Double Int deriving (Show, Generic)
data VBook = VBook String Double deriving (Show, Generic)


bookstore :: MonadError' String m => BiGUL m [SBook] [VBook]
bookstore =
  Align (\_ -> return True)
        (\(SBook stitle _ _ _) (VBook vtitle _) -> return $ stitle == vtitle)
        --(Update (UChild ()))
        (Rearr (EProd (EProd (EPath (SChild (SProdL (STip)))) (EConst ())) (EProd (EPath (SChild (SProdR (STip)))) (EConst ()))) (Update (UChild (UProd (UProd (UVar Replace) (UVar Skip)) (UProd (UVar Replace) (UVar Skip))))))
        (\(VBook vtitle vprice) -> return $ SBook vtitle [] vprice 2012 )
        (\_ -> return Nothing)

{-

bookstore :: MonadError' String m => BiGUL m [SBook] [VBook]
bookstore =
  Align (const (return True))
        (\(SBook stitle _ _ _) (VBook vtitle _) -> return (stitle == vtitle))
        (Rearr ((EPath (SChild (SProdL STip)) `EProd` EConst ()) `EProd` (EPath (SChild (SProdR STip)) `EProd` (EConst ())))
               (Update (UChild ((UVar Replace `UProd` UVar Skip) `UProd` (UVar Replace `UProd` UVar Skip)))))
        (\(VBook title price) -> return (SBook title [] price 0))
        (const (return Nothing))

-}

{-

data BiGUL = Fail
           | Skip
           | Replace -- id_lens: get is id, put ignore s
           | Rearr XQExpr BiGUL
           | Iter BiGUL -- map on list.
           | Align (s -> m Bool)
                   (s -> v -> m Bool)
                   BiGUL
                   (v -> m s)
                   (s -> m (Maybe s)) -- may have deletion on s.
           | CaseS [(s -> m Bool, Either (s -> m s) BiGUL)]
           | CaseV [(Pat, BiGUL)]
           | Update Pat
        deriving (Eq,Show)


data XQExpr = XQEmpty              -- ()
            | XQProd XQExpr XQExpr        -- e,e'
            | XQElem String XQExpr        -- n[e] when we construct an element we must put all attributes first and sorted
            | XQAttr String XQExpr        -- @n='e'
--            | XQString String          -- w
--            | XQVar XVar            -- x (any variable)
            | XQLet Pat XQExpr XQExpr      -- let x = e in e'
--            | XQBool Bool            -- true | false
            | XQIf XQExpr XQExpr XQExpr      -- if c then e else e'
            | XQBinOp XPath.Op XQExpr XQExpr  -- e ~~ e'
            | XQFor XVar XQExpr XQExpr      -- for x- \in e return e' (still for tree variables)
            | XQPath CPath            -- special case to consider core paths (since their implementation as core uXQ is very different)
  deriving (Eq,Show)

type XVar = String

-}
