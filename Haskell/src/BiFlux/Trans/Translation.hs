module BiFlux.Trans.Translation where

import Lang.AST
import Lang.MonadBiGULError
import Control.Monad
import Control.Mand.Except
import GHC.InOut
import BiFlux.Lang.AST
import BiFlux.DTD.Type


--stmt2bigul :: (MonadError Doc m, MonadError' ErrorInfo m') => Stmt -> Type s -> Type v -> m (BiGUL m' s v)
