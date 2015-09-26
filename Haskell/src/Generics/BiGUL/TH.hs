{-# LANGUAGE TupleSections, DeriveDataTypeable #-}
module Generics.BiGUL.TH 
	(
    ConTagSeq(..),
		lookupNames, -- for temporary usage, will be deleted later.
		deriveBiGULGeneric 
	)
where
import Data.Data
import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Control.Monad


data ConTag = L | R 
    deriving (Show, Data, Typeable)

contag :: a -> a -> ConTag -> a
contag a1 _  L = a1
contag _  a2 R = a2


class ConTagSeq a where
  toConTags :: a -> Name -> [ConTag]


type TypeConstructor = String
type ValueConstructor = String 
type ErrorMessage = String


lookupName :: (String -> Q (Maybe Name)) -> ErrorMessage -> String -> Q Name 
lookupName f errMsg name = f name >>= maybe (fail errMsg) return

-- ["Generic", "K1", "U1", ":+:", ":*:", "Rep"]
lookupNames :: [TypeConstructor] -> [ValueConstructor] -> ErrorMessage -> Q ([Name], [Name])
lookupNames typeCList valueCList errMsg = liftM2 (,) (mapM (lookupName lookupTypeName  errMsg) typeCList) 
                                                     (mapM (lookupName lookupValueName errMsg) valueCList)

-- Find the Type Dec by Name
-- Construct an InstanceDec.
deriveBiGULGeneric :: Name -> Q [InstanceDec]
deriveBiGULGeneric name = do
  (name, constructors) <- 
    do
      info <- reify name
      case info of
        (TyConI (DataD [] name [] constructors _)) -> return (name, constructors)
        _            -> fail ( "cannot find " ++ nameBase name ++ ", or not a (supported) datatype.")
  ([nGeneric, nRep, nK1, nR, nU1, nSum, nProd, nV1], [vFrom, vTo, vK1, vL1, vR1, vU1, vProd]) <-
    lookupNames [ "GHC.Generics." ++ s | s <- ["Generic", "Rep", "K1", "R", "U1", ":+:", ":*:", "V1"] ]
                [ "GHC.Generics." ++ s | s <- ["from", "to", "K1", "L1", "R1", "U1", ":*:"] ]
                "cannot find type/value constructors from GHC.Generics."
  ([nConTagSeq], [vToConTags]) <- lookupNames ["Generics.BiGUL.TH." ++ s | s <- ["ConTagSeq"]] ["Generics.BiGUL.TH." ++ s | s <- ["toConTags"]] "cannot find type/value constructors from Generics.BiGUL.TH"  
  env <- consToEnv constructors
  let fromClauses = map (constructFuncFromClause (vK1, vU1, vL1, vR1, vProd)) env
  let toClauses   = map (constructFuncToClause (vK1, vU1, vL1, vR1, vProd)) env 
  conTagsClause <- toconTagsClause env
  return $ [InstanceD [] 
                     (AppT (ConT nGeneric) (ConT name)) 
                     [TySynInstD nRep 
                                 (TySynEqn 
                                    [ConT name] 
                                    (constructorsToSum (nSum, nV1) (map (constructorToProduct (nK1, nR, nU1, nProd)) constructors))), 
                      FunD vFrom fromClauses,
                      FunD vTo toClauses ],
            InstanceD [] 
                      (AppT (ConT nConTagSeq) (ConT name)) 
                      [FunD vToConTags [conTagsClause]]
            ]        

toconTagsClause :: [(Name, [ConTag], [Name])] -> Q Clause
toconTagsClause env = do
  (_, [vEq, vError]) <- lookupNames [] ["==", "error"] "cannot find functions for eq or error."               
  conTagsVarName <- newName "name"
  expEnv <- mapM (\(n, conTags, _) -> liftM2 (,) (dataToExpQ (const Nothing) n) (dataToExpQ (const Nothing) conTags)) env
  let conTagsClauseBody = (foldr (\(nExp, lrsExp) e -> CondE ((VarE vEq `AppE` nExp) `AppE` VarE conTagsVarName) lrsExp e) 
                (VarE vError `AppE` LitE (StringL "cannot find name.")) 
                expEnv)
  return $ Clause [WildP, VarP conTagsVarName] (NormalB conTagsClauseBody) []



constructorsToSum :: (Name, Name) -> [Type] -> Type
constructorsToSum (sum, v1) []  = ConT v1 -- empty
constructorsToSum (sum, v1) tps = foldr1 (\t1 t2 -> (ConT sum `AppT` t1) `AppT` t2) tps


constructorToProduct :: (Name, Name, Name, Name) -> Con -> Type
constructorToProduct (k1, r, u1, prod) (NormalC _ [] ) = ConT u1 
constructorToProduct (k1, r, u1, prod) (NormalC _ sts) = foldr1 (\t1 t2 -> (ConT prod `AppT` t1 ) `AppT` t2) $ map (AppT (ConT k1 `AppT` ConT r) . snd) sts 
constructorToProduct _ _ = error "not supported Con"


constructorToPatAndBody :: Con -> Q (Name, [Name])
constructorToPatAndBody (NormalC name sts) = liftM (name,) $ replicateM (length sts) (newName "var")
constructorToPatAndBody _ = fail "not supported Cons"


zipWithLRs :: [(Name, [Name])] ->  [(Name, [ConTag], [Name])]
zipWithLRs nns = zipWith (\(n, ns) lrs -> (n, lrs, ns)) nns (constructLRs (length nns)) 

consToEnv :: [Con] -> Q [(Name, [ConTag], [Name])]
consToEnv cons = liftM zipWithLRs $ mapM constructorToPatAndBody cons

constructFuncFromClause :: (Name, Name, Name, Name, Name) -> (Name, [ConTag], [Name]) -> Clause
constructFuncFromClause (vK1, vU1, vL1, vR1, vProd) (n, lrs, names) =  Clause [ConP n (map VarP names)] (NormalB (wrapLRs lrs (deriveGeneric names))) []
  where
    wrapLRs :: [ConTag] -> Exp -> Exp
    wrapLRs lrs exp = foldr (\lr e -> ConE (contag vL1 vR1 lr) `AppE` e) exp lrs

    deriveGeneric :: [Name] -> Exp
    deriveGeneric []    = ConE vU1
    deriveGeneric names = foldr1 (\e1 e2 -> (ConE vProd `AppE` e1) `AppE` e2) $ map ((ConE vK1 `AppE`) . VarE) names


constructFuncToClause :: (Name, Name, Name, Name, Name) -> (Name, [ConTag], [Name])  -> Clause
constructFuncToClause (vK1, vU1, vL1, vR1, vProd) (n, lrs, names)  = Clause [wrapLRs lrs (deriveGeneric names)] (NormalB (foldl (\e1 name -> e1 `AppE` (VarE name)) (ConE n) names) ) []
  where
    wrapLRs :: [ConTag] -> Pat -> Pat
    wrapLRs lrs pat = foldr (\lr p -> ConP (contag vL1 vR1 lr) [p]) pat lrs

    deriveGeneric :: [Name] -> Pat
    deriveGeneric []    = ConP vU1 []
    deriveGeneric names = foldr1 (\p1 p2 -> ConP vProd [p1, p2]) $ map (ConP vK1 . (:[]) . VarP) names
  

constructLRs :: Int -> [[ConTag]]
constructLRs 0 = []
constructLRs 1 = [[]]
constructLRs n = [L] : map (R:) (constructLRs (n-1))


