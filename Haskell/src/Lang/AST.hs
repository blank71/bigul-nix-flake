{-# LANGUAGE GADTs, KindSignatures, MultiParamTypeClasses, FlexibleContexts, FlexibleInstances, DeriveGeneric #-}
module Lang.AST where

import Control.Monad.Except
import GHC.Generics
import GHC.InOut
import Text.PrettyPrint

class MonadError e m => MonadError' e m where
  catchBind :: m a -> (a -> m b) -> (e -> m b) -> m b

instance MonadError' e (Either e) where
  -- catchBind :: Either e a -> (a -> Either e b) -> (e -> Either e b) -> Either e b
  catchBind ma f g = either g f ma


class PrettyPrintable s where
  pPrint :: s -> Doc

--instance PrettyPrintable s where


-- break point (expression), source, view, inner error info.
data ErrorInfo = ErrorInfo String

-- | storing error information
-- simplified error information
-- break point (expression)
-- current source
-- current view
-- inner structured error informations
--data ErrorInfo where
--  ErrorInfo :: (PrettyPrintable s, PrettyPrintable v) => Doc -> Doc -> s -> v -> [ErrorInfo] -> ErrorInfo

data Pat :: * -> * -> *  where
  PVar   :: Pat a a
  PConst :: Eq a => a -> Pat a ()
  PProd  :: Pat a a' -> Pat b b' -> Pat (a, b) (a', b')
  PLeft  :: Pat a a' -> Pat (Either a b) a'
  PRight :: Pat b b'  -> Pat (Either a b) b'
  POut :: InOut a => Pat (F a) b -> Pat a b
  PElem  :: Pat a b -> Pat [a] b' -> Pat [a] (b, b')

deconstruct :: MonadError' ErrorInfo m => Pat a b -> a -> m b
deconstruct  PVar             x         = return x
deconstruct (PConst y)        x         = if x == y then return () else throwError $ ErrorInfo "unmatched constant pattern"
deconstruct (PProd lpat rpat) (x, y)    = liftM2 (,) (deconstruct lpat x) (deconstruct rpat y)
deconstruct (PLeft  pat)      (Left  x) = deconstruct pat x
deconstruct (PLeft  pat)      (Right y) = throwError $ ErrorInfo  "left pattern for right value"
deconstruct (PRight pat)      (Left  x) = throwError $ ErrorInfo "right pattern for left value"
deconstruct (PRight pat)      (Right y) = deconstruct pat y
deconstruct (POut pat)      x         = deconstruct pat (out x)
deconstruct (PElem hpat tpat) []        = throwError $ ErrorInfo "head-tail pattern for empty list"
deconstruct (PElem hpat tpat) (x : xs)  = liftM2 (,) (deconstruct hpat x) (deconstruct tpat xs)

construct :: Pat a b -> b -> a
construct  PVar             x      = x
construct (PConst y)        _      = y
construct (PProd lpat rpat) (x, y) = (construct lpat x, construct rpat y)
construct (PLeft  pat)      x      = Left  (construct pat x)
construct (PRight pat)      y      = Right (construct pat y)
construct (POut pat)      x      = inn (construct pat x)
construct (PElem hpat tpat) (x, y) = construct hpat x : construct tpat y


-- construct' :: MonadError' ErrorInfo m =>  Pat a b c -> c -> m b
-- construct' PVar              (Just x) = return x
-- construct' PVar              Nothing  = throwError $ ErrorInfo "Nothing"
-- construct' (PConst c)        ()       = return ()
-- construct' (PProd lpat rpat) (l, r)   =
--   catchBind (construct' lpat l)
--             (\l' -> catchBind (construct' rpat r) (\r' -> return (l', r')) (\e -> throwError $ ErrorInfo "product right failed.")
--               )
--             (\e -> throwError $ ErrorInfo "product left failed.")
-- construct' (PLeft pat)      c        = catchError (construct' pat c) (\e -> throwError $ ErrorInfo "Either Left failed.")
-- construct' (PRight pat)     c        = catchError (construct' pat c) (\e -> throwError $ ErrorInfo "Either Right failed.")
-- construct' (POut pat)     c        = construct' pat c
-- construct' (PElem path patt) (ch, ct) =
--   catchBind (construct' path ch)
--             (\ch' -> catchBind (construct' patt ct) (\ct' -> return (ch', ct')) (\e -> throwError $ ErrorInfo "Element pattern, tail fail.")
--               )
--             (\e -> throwError $ ErrorInfo "Element pattern, head fail")


data UPat :: (* -> *) -> * -> * -> * where
  UVar   :: BiGUL m s v -> UPat m s v
  UConst :: Eq s => s -> UPat m s ()
  UProd  :: UPat m s v -> UPat m s' v' -> UPat m (s, s') (v, v')
  ULeft  :: UPat m s v -> UPat m (Either s s') v
  URight :: UPat m s' v -> UPat m (Either s s') v
  UOut :: InOut s => UPat m (F s) v -> UPat m s v
  UElem  :: UPat m s v -> UPat m [s] v' -> UPat m [s] (v, v')

data CaseSBranch m s v = Normal (BiGUL m s v) | Adaptive (s -> m s)

data CaseVBranch m s v where
  CaseVBranch :: Pat v v' -> BiGUL m s v' -> CaseVBranch m s v

data BiGUL :: (* -> *) -> * -> * -> * where
  Fail    :: BiGUL m s v
  Skip    :: BiGUL m s ()
  Replace :: BiGUL m s s
  Update  :: UPat m s v -> BiGUL m s v
  Rearr   :: RPat v env con -> Expr env v' -> BiGUL m s v' -> BiGUL m s v
  Dep     :: (Eq v') => (v -> v') -> BiGUL m s v -> BiGUL m s (v, v')
  CaseS   :: [(s -> m Bool, CaseSBranch m s v)] -> BiGUL m s v
  CaseV   :: [CaseVBranch m s v] -> BiGUL m s v
  Align   :: (s -> m Bool)
          -> (s -> v -> m Bool)
          -> BiGUL m s v
          -> (v -> m s)
          -> (s -> m (Maybe s))
          -> BiGUL m [s] [v]

newtype Var a = Var a

-- RPat (view type) (environment type) (container type)
data RPat :: * -> * -> * -> * where
  RVar   :: RPat a (Var a) (Maybe a)
  RConst :: Eq a => a -> RPat a () ()
  RProd  :: RPat a a' a'' -> RPat b b' b'' -> RPat (a, b) (a', b') (a'', b'')
  RLeft  :: RPat a a' a'' -> RPat (Either a b) a' a''
  RRight :: RPat b b' b'' -> RPat (Either a b) b' b''
  ROut :: InOut a => RPat (F a) b c -> RPat a b c
  RElem  :: RPat a b c -> RPat [a] b' c' -> RPat [a] (b, b') (c, c')

{-

deconstructR :: MonadError' ErrorInfo m => RPat v env con -> v -> m env
constructR   :: MonadError' ErrorInfo m => RPat v env con -> con -> m v

emptyContainer :: RPat v env con -> con

-}

-- You need explicitly specify the type arguments at the type level when using the Direction type.
-- From type, you could know the type of the data you want.
data Direction :: * -> * -> * where
  DVar    :: Direction (Var a) a
  DMaybe  :: Direction (Maybe a) (Maybe a)
  DLeft   :: Direction a t -> Direction (a, b) t
  DRright :: Direction b t -> Direction (a, b) t

retrieve :: Direction a t -> a -> t
retrieve  DVar      (Var x) = x
retrieve  DMaybe    mx      = mx
retrieve (DLeft  p) (x, y)  = retrieve p x
retrieve (DRight p) (x, y)  = retrieve p y

data Expr :: * -> * -> * where
  EDir   :: Direction orig a -> Expr orig a
  EConst :: (Eq a) =>  a -> Expr orig a
  EIn    :: InOut a => Expr orig (F a) -> Expr orig a
  EProd  :: Expr orig a -> Expr orig b -> Expr orig (a, b)
  ELeft  :: Expr orig a -> Expr orig (Either a b)
  ERight :: Expr orig b -> Expr orig (Either a b)
  EElem  :: Expr orig a -> Expr orig [a] -> Expr orig [a]

{-

eval   :: Expr env v' -> env -> v'
uneval :: (MonadError' ErrorInfo m, Eq v') => RPat v env con -> Expr env v' -> con -> v' -> m con

-}

data SBook = SBook String [String] Double Int deriving (Show, Generic)
data VBook = VBook String Double deriving (Show, Generic)

{-

bookstore :: MonadError' String m => BiGUL m [SBook] [VBook]
bookstore =
  Align (\_ -> return True)
        (\(SBook stitle _ _ _) (VBook vtitle _) -> return $ stitle == vtitle)
        (Rearr (POut PVar)(EProd (EProd (EPath (SL ST)) (EConst ())) (EProd (EPath (SR ST)) (EConst ()))) (Update (UOut (UProd (UProd (UVar Replace) (UVar Skip)) (UProd (UVar Replace) (UVar Skip))))))
        (\(VBook vtitle vprice) -> return $ SBook vtitle [] vprice 2012 )
        (\_ -> return Nothing)

bookstore :: MonadError' String m => BiGUL m [SBook] [VBook]
bookstore =
  Align (const (return True))
        (\(SBook stitle _ _ _) (VBook vtitle _) -> return (stitle == vtitle))
        (Rearr ((EPath (SOut (SProdL STip)) `EProd` EConst ()) `EProd` (EPath (SOut (SProdR STip)) `EProd` (EConst ())))
               (Update (UOut ((UVar Replace `UProd` UVar Skip) `UProd` (UVar Replace `UProd` UVar Skip)))))
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
