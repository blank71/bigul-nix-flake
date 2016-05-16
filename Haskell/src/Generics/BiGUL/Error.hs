module Generics.BiGUL.Error where

import Generics.BiGUL

import GHC.InOut

import Text.PrettyPrint


-- | A class of types that can be printed to `Text.PrettyPrint.Doc`.
class PrettyPrintable a where
  pPrint :: a -> Doc

data PutError s v where
  PFail                      :: String -> PutError s v
  PSkipMismatch              :: PutError s v
  PSourcePatternMismatch     :: PatExprDirError s -> PutError s v
  PViewPatternMismatch       :: PatExprDirError v -> PutError s v
  PUnevalFailed              :: PatExprDirError s' -> PutError s v
  PDependencyMismatch        :: PutError s (v, v')
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
  show  PDependencyMismatch          = "dependency mismatch"
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
  show (PBranch _ e)                 = show e

indent :: Doc -> Doc
indent = nest 2

instance PrettyPrintable (PutError s v) where
  pPrint e@(PFail str)                = text (show e)
  pPrint (PSourcePatternMismatch e)   = text "source pattern mismatch" $+$ indent (pPrint e)
  pPrint (PViewPatternMismatch e)     = text "view pattern mismatch" $+$ indent (pPrint e)
  pPrint (PUnevalFailed e)            = text "inverse evaluation failed" $+$ indent (pPrint e)
  pPrint e@PDependencyMismatch        = text (show e)
  pPrint (PNoIntermediateSource e)    = text "computation of intermediate source failed" $+$ indent (pPrint e)
  pPrint e@PCaseExhausted             = text (show e)
  pPrint e@PAdaptiveBranchRevisited   = text (show e)
  pPrint e@PAdaptiveBranchMatched     = text (show e)
  pPrint e@PPreviousBranchMatched     = text (show e)
  pPrint e@PBranchPredictionIncorrect = text (show e)
  pPrint e@PPostVerificationFailed    = text (show e)
  pPrint e@PBranchUnmatched           = text (show e)
  pPrint (PProdLeft _ _ e)            = text "on the left-hand side of Prod" $+$ pPrint e
  pPrint (PProdRight _ _ e)           = text "on the right-hand side of Prod" $+$ pPrint e
  pPrint (PRearrS _ _ e)              = text "in RearrS" $+$ pPrint e
  pPrint (PRearrV _ _ e)              = text "in RearrV" $+$ pPrint e
  pPrint (PDep _ _ e)                 = text "in Dep" $+$ pPrint e
  pPrint (PComposeLeft _ _ e)         = text "on the left-hand side of Comp" $+$ pPrint e
  pPrint (PComposeRight _ _ e)        = text "on the right-hand side of Comp" $+$ pPrint e
  pPrint (PBranch i e)                = text ("in Case branch " ++ show i) $+$ pPrint e

data GetError s v where
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
  show  GAdaptiveBranchMatched       = "adaptive branch matched"
  show (GProdLeft _ e)               = show e
  show (GProdRight _ e)              = show e
  show (GRearrS _ e)                 = show e
  show (GRearrV _ e)                 = show e
  show (GDep _ e)                    = show e
  show (GComposeLeft _ e)            = show e
  show (GComposeRight _ e)           = show e
  show (GBranch _ e)                 = show e

instance PrettyPrintable (GetError s v) where
  pPrint e@(GFail str)                 = text (show e)
  pPrint (GSourcePatternMismatch e)    = text "source pattern mismatch" $+$ indent (pPrint e)
  pPrint (GUnevalFailed e)             = text "inverse evaluation failed" $+$ indent (pPrint e)
  pPrint (GViewRecoveringIncomplete e) = text "view recovering incomplete" $+$ indent (pPrint e)
  pPrint e@(GCaseExhausted es)         = text (show e) $+$
                                                foldr ($+$) empty
                                                  (zipWith (\i doc -> text ("branch " ++ show i) $+$ indent doc)
                                                           [0..]
                                                           (map pPrint es))
  pPrint e@GPreviousBranchMatched      = text (show e)
  pPrint e@GPostVerificationFailed     = text (show e)
  pPrint e@GBranchUnmatched            = text (show e)
  pPrint e@GAdaptiveBranchMatched      = text (show e)
  pPrint (GProdLeft _ e)               = text "on the left-hand side of Prod" $+$ pPrint e
  pPrint (GProdRight _ e)              = text "on the right-hand side of Prod" $+$ pPrint e
  pPrint (GRearrS _ e)                 = text "in RearrS" $+$ pPrint e
  pPrint (GRearrV _ e)                 = text "in RearrV" $+$ pPrint e
  pPrint (GDep _ e)                    = text "in Dep" $+$ pPrint e
  pPrint (GComposeLeft _ e)            = text "on the left-hand side of Comp" $+$ pPrint e
  pPrint (GComposeRight _ e)           = text "on the right-hand side of Comp" $+$ pPrint e
  pPrint (GBranch i e)                 = text ("in Case branch " ++ show i) $+$ pPrint e

data PatExprDirError a where
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

instance PrettyPrintable (PatExprDirError a) where
  pPrint e@PEDConstantMismatch          = text (show e)
  pPrint e@PEDEitherMismatch            = text (show e)
  pPrint e@PEDValueUnrecoverable        = text (show e)
  pPrint e@(PEDIncompatibleUpdates _ _) = text (show e)
  pPrint e@(PEDMultipleUpdates _ _)     = text (show e)
  pPrint (PEDProdLeft e)                = text "on the left-hand side of PProd" $+$ pPrint e
  pPrint (PEDProdRight e)               = text "on the right-hand side of PProd" $+$ pPrint e
  pPrint (PEDEitherLeft e)              = text "inside PLeft" $+$ pPrint e
  pPrint (PEDEitherRight e)             = text "inside PRight" $+$ pPrint e
  pPrint (PEDIn e)                      = text "inside PIn" $+$ pPrint e

liftE :: (a -> b) -> Either a c -> Either b c
liftE f = either (Left . f) Right

data BiGULType a where
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

pPrint' :: BiGULType a -> a -> Doc
pPrint' (BProd   t u) (x, y)    = parens (pPrint' t x <> comma <+> pPrint' u y)
pPrint' (BEither t u) (Left  x) = text "Left" <+> pPrint' t x
pPrint' (BEither t u) (Right y) = text "Right" <+> pPrint' u y
pPrint' (BData   t  ) x         = pPrint x

-- pPrint :: BiGULTypable a => a -> Doc
-- pPrint = pPrint' getBiGULType
