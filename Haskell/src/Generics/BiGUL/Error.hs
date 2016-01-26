{-# LANGUAGE UndecidableInstances #-}

module Generics.BiGUL.Error where

import GHC.InOut
import Text.PrettyPrint

data PutError :: * -> * -> * where
  PFail                      :: String -> PutError s v
  PSourcePatternMismatch     :: PatExprDirError s -> PutError s v
  PViewPatternMismatch       :: PatExprDirError v -> PutError s v
  PUnevalFailed              :: PatExprDirError s' -> PutError s v
  PViewRecoveringIncomplete  :: PatExprDirError v' -> PutError s v
  PDependencyMismatch        :: s -> PutError s (v, v')
  PNoIntermediateSource      :: GetError s v' -> PutError s v
  PCaseExhausted             :: PutError s v
  PAdaptiveBranchRevisited   :: PutError s v
  PAdaptiveBranchMatched     :: PutError s v
  PPreviousBranchMatched     :: PutError s v
  PBranchPredictionIncorrect :: PutError s v
  PPostVerificationFailed    :: PutError s v
  PBranchUnmatched           :: PutError s v
  --
  PProdLeft     :: s -> v -> PutError s v -> PutError (s, s') (v, v')
  PProdRight    :: s' -> v' -> PutError s' v' -> PutError (s, s') (v, v')
  PRearrS       :: s' -> v -> PutError s' v -> PutError s v
  PRearrV       :: s -> v' -> PutError s v' -> PutError s v
  PDep          :: s -> v -> PutError s v -> PutError s (v, v')
  PComposeLeft  :: a -> b -> PutError a b -> PutError a c
  PComposeRight :: b -> c -> PutError b c -> PutError a c
  PBranch       :: Int -> PutError s v -> PutError s v

incrBranchNo :: PutError s v -> PutError s v
incrBranchNo (PBranch i e) = PBranch (i+1) e
incrBranchNo e              = e

instance Show (PutError s v) where
  show (PFail str)                   = "fail: " ++ str
  show (PSourcePatternMismatch e)    = show e
  show (PViewPatternMismatch e)      = show e
  show (PUnevalFailed e)             = show e
  show (PViewRecoveringIncomplete e) = show e
  show (PDependencyMismatch _)       = "dependency mismatch"
  show (PNoIntermediateSource e)     = show e
  show  PCaseExhausted               = "case exhausted"
  show  PAdaptiveBranchRevisited     = "adaptive branch revisited"
  show  PAdaptiveBranchMatched       = "adaptive branch matched"
  show  PPreviousBranchMatched       = "previous branch matched"
  show  PBranchPredictionIncorrect   = "branch prediction incorrect"
  show  PPostVerificationFailed      = "post-verification failed"
  show  PBranchUnmatched             = "branch unmatched"
  show (PProdLeft _ _ e)             = show e
  show (PProdRight _ _ e)            = show e
  show (PRearrS _ _ e)               = show e
  show (PRearrV _ _ e)               = show e
  show (PDep _ _ e)                  = show e
  show (PComposeLeft _ _ e)          = show e
  show (PComposeRight _ _ e)         = show e
  show (PBranch i e)                 = show e

data GetError :: * -> * -> * where
  GFail                      :: String -> GetError s v
  GSourcePatternMismatch     :: PatExprDirError s -> GetError s v
  GUnevalFailed              :: PatExprDirError s' -> GetError s v
  GViewRecoveringIncomplete  :: PatExprDirError v' -> GetError s v
  GCaseExhausted             :: [GetError s v] -> GetError s v
  GPreviousBranchMatched     :: GetError s v
  GPostVerificationFailed    :: GetError s v
  GBranchUnmatched           :: GetError s v
  GAdaptiveBranchMatched     :: GetError s v
  --
  GProdLeft     :: s -> GetError s v -> GetError (s, s') (v, v')
  GProdRight    :: s' -> GetError s' v' -> GetError (s, s') (v, v')
  GRearrS       :: s' -> GetError s' v -> GetError s v
  GRearrV       :: s -> GetError s v' -> GetError s v
  GDep          :: s -> GetError s v -> GetError s (v, v')
  GComposeLeft  :: a -> GetError a b -> GetError a c
  GComposeRight :: b -> GetError b c -> GetError a c
  GBranch       :: Int -> GetError s v -> GetError s v

addCurrentBranchError :: GetError s v -> GetError s v -> GetError s v
addCurrentBranchError e0 (GCaseExhausted es) = GCaseExhausted (e0:es)
addCurrentBranchError e0 (GBranch i e) = GBranch (i+1) e

instance Show (GetError s v) where
  show (GFail str)                   = "fail: " ++ str
  show (GSourcePatternMismatch e)    = show e
  show (GUnevalFailed e)             = show e
  show (GViewRecoveringIncomplete e) = show e
  show (GCaseExhausted _)            = "case exhausted"
  show  GPreviousBranchMatched       = "previous branch matched"
  show  GPostVerificationFailed      = "post-verification failed"
  show  GBranchUnmatched             = "branch unmatched"
  show (GProdLeft _ e)               = show e
  show (GProdRight _ e)              = show e
  show (GRearrS _ e)                 = show e
  show (GRearrV _ e)                 = show e
  show (GDep _ e)                    = show e
  show (GComposeLeft _ e)            = show e
  show (GComposeRight _ e)           = show e
  show (GBranch _ e)                 = show e

data PatExprDirError :: * -> * where
  PEDConstantMismatch    :: PatExprDirError a
  PEDEitherMismatch   :: PatExprDirError (Either a b)
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
  show  PEDConstantMismatch         = "constant mismatch"
  show  PEDEitherMismatch           = "either value mismatch"
  show  PEDValueUnrecoverable       = "value unrecoverable"
  show (PEDIncompatibleUpdates _ _) = "incompatible updates"
  show (PEDMultipleUpdates _ _)     = "multiple updates"
  show (PEDProdLeft e)              = show e
  show (PEDProdRight e)             = show e
  show (PEDEitherLeft e)            = show e
  show (PEDEitherRight e)           = show e
  show (PEDIn e)                    = show e

liftE :: (a -> b) -> Either a c -> Either b c
liftE f = either (Left . f) Right

class PrettyPrintable a where
  toDoc :: a -> Doc

data BiGULType :: * -> * where
  BProd   :: BiGULType a -> BiGULType b -> BiGULType (a, b)
  BEither :: BiGULType a -> BiGULType b -> BiGULType (Either a b)
  BData   :: (InOut a, PrettyPrintable a) => BiGULType (F a) -> BiGULType a

instance Show (BiGULType a) where
  show (BProd   t u) = "(Prod " ++ show t ++ " " ++ show u ++ ")"
  show (BEither t u) = "(BEither " ++ show t ++ " " ++ show u ++ ")"
  show (BData   _  ) = "BData"

class  BiGULTypable a where
  getBiGULType :: BiGULType a

instance {-# OVERLAPPING #-} (BiGULTypable a, BiGULTypable b) => BiGULTypable (a, b) where
  getBiGULType = getBiGULType `BProd` getBiGULType

instance {-# OVERLAPPING #-} (BiGULTypable a, BiGULTypable b) => BiGULTypable (Either a b) where
  getBiGULType = getBiGULType `BEither` getBiGULType

instance {-# OVERLAPPABLE #-} (InOut a, PrettyPrintable a, BiGULTypable (F a)) => BiGULTypable a where
  getBiGULType = BData getBiGULType

pprint' :: BiGULType a -> a -> Doc
pprint' (BProd   t u) (x, y)    = parens (pprint' t x <> comma <+> pprint' u y)
pprint' (BEither t u) (Left  x) = text "Left" <+> pprint' t x
pprint' (BEither t u) (Right y) = text "Right" <+> pprint' u y
pprint' (BData   t  ) x         = toDoc x

pprint :: BiGULTypable a => a -> Doc
pprint = pprint' getBiGULType
