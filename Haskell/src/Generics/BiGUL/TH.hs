module Generics.BiGUL.TH where
import Language.Haskell.TH
import Control.Monad


-- Help function: lookup type constructor name by a given string.
lookupTypeConstructor :: TypeConstructor -> ErrorMessage -> Q Name
lookupTypeConstructor name errMsg = lookupTypeName name >>= maybe (fail errMsg) return

-- Help function: lookup value constructor name by a given string.
lookupValueConstructor :: ValueConstructor -> ErrorMessage -> Q Name
lookupValueConstructor name errMsg = lookupValueName name >>= maybe (fail errMsg) return

-- ["Generic", "K1", "U1", ":+:", ":*:", "Rep"]
type TypeConstructor = String
type ValueConstructor = String 
type ErrorMessage = String
lookupNames :: [TypeConstructor] -> [ValueConstructor] -> ErrorMessage -> Q ([Name], [Name])
lookupNames typeCList valueCList errMsg = liftM2 (,) (mapM (flip lookupTypeConstructor errMsg) typeCList) (mapM (flip lookupValueConstructor errMsg) valueCList)
