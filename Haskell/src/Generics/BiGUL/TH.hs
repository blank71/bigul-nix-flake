-- |
module Generics.BiGUL.TH (
  -- * 'Generic' instance derivation
    deriveBiGULGeneric
  -- * Rearrangement
  , rearrS
  , rearrV
  , update
  -- * 'Case' branch construction
  , normal
  , normalSV
  , adaptive
  , adaptiveSV) where

import Data.Data
import Data.Maybe
import Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import Language.Haskell.TH as TH
import qualified Language.Haskell.TH.Syntax as THS
import Language.Haskell.TH.Quote
import Generics.BiGUL
import Control.Monad



data ConTag = L | R
  deriving (Show, Data, Typeable)


data PatTag = RTag   -- ^ view pattern
            | STag   -- ^ source Pattern
            | ETag   -- ^ expression

instance Show PatTag where
   show ETag = "E"
   show _    = "P"

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
  (name, typeVars, constructors) <-
    do
      info <- reify name
      case info of
        (TyConI (DataD [] name typeVars constructors _)) -> return (name, typeVars, constructors)
        _            -> fail ( "cannot find " ++ nameBase name ++ ", or not a (supported) datatype.")
  ([nGeneric, nRep, nK1, nR, nU1, nSum, nProd, nV1, nS1, nSelector, nDataType], [vFrom, vTo, vK1, vL1, vR1, vU1, vProd, vSelName, vDataTypeName, vModuleName, vM1]) <-
    lookupNames [ "GHC.Generics." ++ s | s <- ["Generic", "Rep", "K1", "R", "U1", ":+:", ":*:", "V1", "S1", "Selector", "Datatype"] ]
                [ "GHC.Generics." ++ s | s <- ["from", "to", "K1", "L1", "R1", "U1", ":*:", "selName", "datatypeName", "moduleName", "M1"] ]
                "cannot find type/value constructors from GHC.Generics."
  env <- consToEnv constructors
  let selectorsNameList =  generateSelectorNames constructors
  let selectorDataDMaybeList = generateSelectorDataD selectorsNameList
  let selectorDataTypeMaybeList = map (generateSelectorDataType nDataType vDataTypeName vModuleName (maybe "" id (nameModule name))) selectorsNameList
  let selectorNameAndConList = zip selectorsNameList constructors
  let selectorInstanceDecList = map (generateSelectorInstanceDec nSelector vSelName) selectorNameAndConList
  let fromClauses = map (constructFuncFromClause (vK1, vU1, vL1, vR1, vProd, vM1)) env
  let toClauses   = map (constructFuncToClause (vK1, vU1, vL1, vR1, vProd, vM1)) env
  --conTagsClause <- toconTagsClause env
  return $ catMaybes selectorDataDMaybeList ++
           catMaybes (concat selectorDataTypeMaybeList) ++
           catMaybes (concat selectorInstanceDecList) ++
           [InstanceD []
                     (AppT (ConT nGeneric) (generateTypeVarsType name typeVars))
                     [TySynInstD nRep
                                 (TySynEqn
                                    [generateTypeVarsType name typeVars]
                                    (constructorsToSum (nSum, nV1) (map (constructorToProduct (nK1, nR, nU1, nProd, nS1)) selectorNameAndConList))),
                      FunD vFrom fromClauses,
                      FunD vTo toClauses ]
            ]


toconTagsClause :: [(Bool, Name, [ConTag], [Name])] -> Q Clause
toconTagsClause env = do
  (_, [vEq, vError]) <- lookupNames [] ["==", "error"] "cannot find functions for eq or error."
  conTagsVarName <- newName "name"
  expEnv <- mapM (\(b, n, conTags, _) -> liftM2 (,) (dataToExpQ (const Nothing) n) (dataToExpQ (const Nothing) conTags)) env
  let conTagsClauseBody = (foldr (\(nExp, lrsExp) e -> CondE ((VarE vEq `AppE` nExp) `AppE` VarE conTagsVarName) lrsExp e)
                (VarE vError `AppE` LitE (StringL "cannot find name."))
                expEnv)
  return $ Clause [WildP, VarP conTagsVarName] (NormalB conTagsClauseBody) []



constructorsToSum :: (Name, Name) -> [Type] -> Type
constructorsToSum (sum, v1) []  = ConT v1 -- empty
constructorsToSum (sum, v1) tps = foldr1 (\t1 t2 -> (ConT sum `AppT` t1) `AppT` t2) tps


constructorToProduct :: (Name, Name, Name, Name, Name) -> ([Maybe Name], Con) -> Type
constructorToProduct (k1, r, u1, prod, s1) (_,     NormalC _ [] ) = ConT u1
constructorToProduct (k1, r, u1, prod, s1) (_,     NormalC _ sts) = foldr1 (\t1 t2 -> (ConT prod `AppT` t1 ) `AppT` t2) $ map (AppT (ConT k1 `AppT` ConT r) . snd) sts
constructorToProduct (k1, r, u1, prod, s1) (names, RecC    _ sts) = foldr1 (\t1 t2 -> (ConT prod `AppT` t1 ) `AppT` t2) $ map (\(Just n, st) -> AppT (ConT s1 `AppT` ConT n) ((ConT k1 `AppT` ConT r) `AppT` third st)) (zip names sts)
constructorToProduct _ _ = error "not supported Con"

third :: (a, b, c) -> c
third  (_, _, z) = z

-- Bool indicates: if Normal then False else RecC True
constructorToPatAndBody :: Con -> Q (Bool, Name, [Name])
constructorToPatAndBody (NormalC name sts) = liftM (False, name,) $ replicateM (length sts) (newName "var")
constructorToPatAndBody (RecC    name sts) = liftM (True, name,) $ replicateM (length sts) (newName "var")
constructorToPatAndBody _ = fail "not supported Cons"


zipWithLRs :: [(Bool, Name, [Name])] ->  [(Bool, Name, [ConTag], [Name])]
zipWithLRs nns = zipWith (\(b, n, ns) lrs -> (b, n, lrs, ns)) nns (constructLRs (length nns))

consToEnv :: [Con] -> Q [(Bool, Name, [ConTag], [Name])]
consToEnv cons = liftM zipWithLRs $ mapM constructorToPatAndBody cons

constructFuncFromClause :: (Name, Name, Name, Name, Name, Name) -> (Bool, Name, [ConTag], [Name]) -> Clause
constructFuncFromClause (vK1, vU1, vL1, vR1, vProd, vM1) (b, n, lrs, names) =  Clause [ConP n (map VarP names)] (NormalB (wrapLRs lrs (deriveGeneric names))) []
  where
    wrapLRs :: [ConTag] -> Exp -> Exp
    wrapLRs lrs exp = foldr (\lr e -> ConE (contag vL1 vR1 lr) `AppE` e) exp lrs

    deriveGeneric :: [Name] -> Exp
    deriveGeneric []    = ConE vU1
    deriveGeneric names = foldr1 (\e1 e2 -> (ConE vProd `AppE` e1) `AppE` e2) $ map (\name -> if b then ConE vM1 `AppE` (ConE vK1 `AppE` VarE name) else ConE vK1 `AppE` VarE name) names


constructFuncToClause :: (Name, Name, Name, Name, Name, Name) -> (Bool, Name, [ConTag], [Name])  -> Clause
constructFuncToClause (vK1, vU1, vL1, vR1, vProd, vM1) (b, n, lrs, names)  = Clause [wrapLRs lrs (deriveGeneric names)] (NormalB (foldl (\e1 name -> e1 `AppE` (VarE name)) (ConE n) names) ) []
  where
    wrapLRs :: [ConTag] -> TH.Pat -> TH.Pat
    wrapLRs lrs pat = foldr (\lr p -> ConP (contag vL1 vR1 lr) [p]) pat lrs

    deriveGeneric :: [Name] -> TH.Pat
    deriveGeneric []    = ConP vU1 []
    deriveGeneric names = foldr1 (\p1 p2 -> ConP vProd [p1, p2]) $ map (\name -> if b then (ConP vM1 ((:[]) (ConP vK1 ((:[]) (VarP name))))) else (ConP vK1 ((:[]) (VarP name)))) names

-- construct selector names from constructors
generateSelectorNames :: [Con] -> [[Maybe Name]]
generateSelectorNames = map (\con ->
  case con of {
      RecC _ sts -> map (\(n, _, _) -> Just (mkName ( "Selector_" ++ nameBase n))) sts;
      _          -> []
    })

generateSelectorDataD :: [[Maybe Name]] -> [Maybe Dec]
generateSelectorDataD names = map (\name -> case name of {Just n -> Just $ DataD [] n [] [] []; Nothing -> Nothing}) (concat names)

-- Selector DataType Generation
generateSelectorDataType :: Name -> Name -> Name -> String -> [Maybe Name] -> [Maybe Dec]
generateSelectorDataType nDataType vDataTypeName vModuleName moduleName = map (generateSelectorDataType' nDataType vDataTypeName vModuleName moduleName)

generateSelectorDataType' :: Name -> Name -> Name -> String -> Maybe Name -> Maybe Dec
generateSelectorDataType' nDataType vDataTypeName vModuleName moduleName (Just selectorName) =
  Just $ InstanceD []
    (AppT (ConT nDataType) (ConT selectorName))
    [FunD vDataTypeName ([Clause [WildP] (NormalB (LitE (StringL (show selectorName)))) []]),
     FunD vModuleName   ([Clause [WildP] (NormalB (LitE (StringL moduleName))) []])
    ]
generateSelectorDataType' nDataType vDataTypeName vModuleName moduleName _ = Nothing

-- Selector Instance Declaration generation
generateSelectorInstanceDec :: Name -> Name -> ([Maybe Name], Con) -> [Maybe Dec]
generateSelectorInstanceDec nSelector vSelName ([]   , _  ) = []
generateSelectorInstanceDec nSelector vSelName (names, (RecC _ sts)) = map (generateSelectorInstanceDec' nSelector vSelName) (zip names sts)

generateSelectorInstanceDec' :: Name -> Name -> (Maybe Name, THS.VarStrictType) -> Maybe Dec
generateSelectorInstanceDec' nSelector vSelName (Just selectorName, (name, _, _)) =
  Just $ InstanceD []
            (AppT (ConT nSelector) (ConT selectorName))
            [FunD vSelName ([Clause [WildP] (NormalB (LitE (StringL (nameBase name)))) []])]
generateSelectorInstanceDec' _         _         _                          = Nothing


-- generate type representation of polymorhpic type
-- e.g. VBook a b is represented as: AppT (ConT name) (ConT name_a `AppT` ConT name_b)
generateTypeVarsType :: Name -> [TyVarBndr] -> Type
generateTypeVarsType n []    = ConT n -- not polymorphic case.
generateTypeVarsType n tvars = foldl (\a b -> AppT a b) (ConT n) $ map (\tvar ->
   case tvar of
    { PlainTV  name      -> VarT name;
      KindedTV name kind -> VarT name-- error "kind type variables are not supported yet."
    }) tvars


constructLRs :: Int -> [[ConTag]]
constructLRs 0 = []
constructLRs 1 = [[]]
constructLRs n = [L] : map (R:) (constructLRs (n-1))

lookupLRs :: Name -> Q [ConTag]
lookupLRs conName = do
  info <- reify conName
  datatypeName <-
    case info of
      DataConI _ _ n _ -> return n
      _ -> fail $ nameBase conName ++ " is not a data constructor"
  TyConI (DataD _ _ _ cons _) <- reify datatypeName
  return $ constructLRs (length cons) !!
             fromJust (List.findIndex (== conName) (map (\con -> case con of { NormalC n _ -> n; RecC n _ -> n}) cons))

lookupRecordLength :: Name -> Q Int
lookupRecordLength conName = do
  info <- reify conName
  datatypeName <-
    case info of
      DataConI _ _ n _ -> return n
      _ -> fail $ nameBase conName ++ " is not a data constructor"
  TyConI (DataD _ _ _ cons _) <- reify datatypeName
  return $ (\(RecC _ fs) -> length fs) (fromJust (List.find (\(RecC n _) -> n == conName) cons))

lookupRecordField :: Name -> Name -> Q Int
lookupRecordField conName fieldName = do
  info <- reify conName
  datatypeName <-
    case info of
      DataConI _ _ n _ -> return n
      _ -> fail $ nameBase conName ++ " is not a data constructor"
  TyConI (DataD _ _ _ cons _) <- reify datatypeName
  case (List.findIndex (\(n,_,_) -> n == fieldName) ((\(RecC _ fs) -> fs) $ fromJust (List.find (\(RecC n _) -> n == conName) cons))) of
       Just res -> return res
       Nothing -> fail $ nameBase fieldName ++ " is not a field in " ++ nameBase conName


mkConstrutorFromLRs :: [ConTag] -> PatTag -> Q (Exp -> Exp)
mkConstrutorFromLRs lrs patTag = do (_, [gin, gleft, gright]) <- lookupNames [] [ "Generics.BiGUL." ++ show patTag ++ s | s <- ["In", "Left", "Right"] ] "cannot find data constructors *what* from Generic.BiGUL"
                                    return $ foldl (.) (AppE (ConE gin)) (map (AppE . ConE . contag gleft gright) lrs)


astNameSpace :: String
astNameSpace = "Generics.BiGUL."

-- |
mkPat :: TH.Pat -> PatTag -> [Name] -> Q TH.Exp

mkPat (LitP c) patTag _ = do
  (_, [gconst]) <- lookupNames [] [astNameSpace ++ show patTag ++ "Const"] (notFoundMsg $ show patTag ++ "Const")
  return $ ConE gconst `AppE` LitE c


-- user defined datatypes && unit pattern
mkPat (ConP name ps) patTag dupnames = do
  ConP name' [] <- [p| () |]
  if name == name' && ps == []
  then do
       unitt         <- [| () |]
       (_, [gconst]) <- lookupNames [] [astNameSpace ++ show patTag ++ s | s <- ["Const"]] (notFoundMsg $ show patTag ++ "Const")
       return $ ConE gconst `AppE` unitt
  else do
       lrs <- lookupLRs name
       conInEither <- mkConstrutorFromLRs lrs patTag
       pes         <- case ps of
                       [] -> mkPat (ConP name' []) patTag dupnames
                       _  -> mkPat (TupP ps)  patTag dupnames
       return $ conInEither pes



mkPat (RecP name ps) patTag dupnames = do
  -- reduce the case for a record constructor to the case for an ordinary constructor
  len <- lookupRecordLength name -- number of constructor arguments
  indexs <- mapM (\(n,_) -> lookupRecordField name n) ps -- positions of the fields mentioned in p
  let nps = map snd ps  -- patterns for the fields
  mkPat (ConP name (helper 0 len (zip indexs nps) [])) patTag dupnames -- grab the pattern for position i for each 0 <= i < len from zip indexs nps
  where findInPair [] i = WildP
        findInPair ((j,p):xs) i | i == j = p
                                | otherwise = findInPair xs i
        helper i n pairs acc  | i == n = acc
                              | otherwise = helper (i+1) n pairs (acc++[findInPair pairs i])
        -- let ips = zip indexs nps in [ maybe WildP id (List.lookup i ips) | i <- [0..len-1] ]


mkPat (ListP []) patTag dupnames = do emptyp <- [p| [] |]
                                      mkPat emptyp patTag dupnames

mkPat (ListP (p:xs)) patTag dupnames = do
  hexp <- mkPat p patTag dupnames
  rexp <- mkPat (ListP xs) patTag dupnames
  (_, [gin,gright,gprod]) <- lookupNames [] [astNameSpace ++ show patTag ++ s | s <- ["In","Right","Prod"]] (notFoundMsg $ (concatWith " ". map (withPatTag patTag)) ["In","Right","Prod"])
  return $ ConE gin `AppE` (ConE gright `AppE` (ConE gprod `AppE` hexp `AppE` rexp))

mkPat (InfixP pl name pr) patTag dupnames = do
  ConE name' <- [| (:) |]
  if name == name'
  then do lpat <- mkPat pl patTag dupnames
          rpat <- mkPat pr patTag dupnames
          (_, [gin,gright,gprod]) <- lookupNames [] [astNameSpace ++ show patTag ++ s | s <- ["In","Right","Prod"]] (notFoundMsg $ (concatWith " ". map (withPatTag patTag)) ["In","Right","Prod"])
          return $ ConE gin `AppE` (ConE gright `AppE` (ConE gprod `AppE` lpat `AppE` rpat))
  else fail $ "constructors mismatch: " ++ nameBase name ++ " and " ++ nameBase name'


mkPat (TupP [p]) patTag dupnames = mkPat p patTag dupnames
mkPat (TupP (p:ps)) patTag dupnames = do
  lexp <- mkPat p patTag dupnames
  rexp <- mkPat (TupP ps) patTag dupnames
  (_, [gprod]) <- lookupNames [] [astNameSpace ++ show patTag ++ s | s <- ["Prod"]] (notFoundMsg "Prod")
  return ((ConE gprod `AppE` lexp) `AppE` rexp)



mkPat (WildP) RTag _ = fail $ "Wildcard(_) connot be used in lambda pattern expression."
mkPat (WildP) STag _ = do
  (_, [pvar'])       <- lookupNames [] [astNameSpace ++ "PVar'"] (notFoundMsg "PVar'")
  return $ ConE pvar'


mkPat (VarP name) _  dupnames =  do
  (_, [pvar,pvar'])       <- lookupNames [] [ astNameSpace ++ s | s <- ["PVar", "PVar'"] ] (notFoundMsg "PVar,PVar'")
  return $ if name `elem` dupnames then ConE pvar else ConE pvar'



mkPat _ patTag _ = fail $ "Pattern not handled yet."









-- | translate all (VarE name) to directions using env
rearrangeExp :: Exp -> Map String Exp -> Q Exp
rearrangeExp (VarE name) env  =
  case Map.lookup (nameBase name) env of
    Just val -> return val
    Nothing  -> fail $ "cannot find name " ++ nameBase name ++ " in env."
rearrangeExp (AppE e1 e2) env = liftM2 AppE (rearrangeExp e1 env) (rearrangeExp e2 env)
rearrangeExp (ConE name) env  = return $ ConE name
rearrangeExp (LitE c)    env  = return $ LitE c
rearrangeExp _           env  = fail $ "Invalid representation of bigul program in TemplateHaskell ast"









mkEnvForRearr :: TH.Pat -> Q (Map String Exp)
mkEnvForRearr (LitP c) = return Map.empty

-- empty list is ok , mkEnvForRearr return Q Map.empty for it
mkEnvForRearr (ConP name ps) = mkEnvForRearr (TupP ps)

mkEnvForRearr (RecP name ps) = do
  len <- lookupRecordLength name
  indexs <- mapM (\(n,_) -> lookupRecordField name n) ps
  let nps = map snd ps
  mkEnvForRearr (ConP name (helper 0 len (zip indexs nps) []))
  where findInPair [] i = WildP
        findInPair ((j,p):xs) i | i == j = p
                                | otherwise = findInPair xs i
        helper i n pairs acc  | i == n = acc
                              | otherwise = helper (i+1) n pairs (acc++[findInPair pairs i])

mkEnvForRearr (ListP []) = return Map.empty
mkEnvForRearr (ListP (pl:pr))     = do
  (_, [dleft,dright]) <- lookupNames [] [ astNameSpace ++ s | s <- ["DLeft", "DRight"] ] (notFoundMsg "DLeft, DRight")
  lenv <- mkEnvForRearr pl
  renv <- mkEnvForRearr (ListP pr)
  return $ Map.map (ConE dleft `AppE`) lenv `Map.union`
          Map.map (ConE dright `AppE`) renv

mkEnvForRearr (InfixP pl name pr) = do
  (_, [dleft,dright]) <- lookupNames [] [ astNameSpace ++ s | s <- ["DLeft", "DRight"] ] (notFoundMsg "DLeft, DRight")
  lenv <- mkEnvForRearr pl
  renv <- mkEnvForRearr pr
  return $ Map.map (ConE dleft `AppE`) lenv `Map.union`
          Map.map (ConE dright `AppE`) renv

mkEnvForRearr (TupP ps) = do
  (_, [dleft,dright]) <- lookupNames [] [ astNameSpace ++ s | s <- ["DLeft", "DRight"] ] (notFoundMsg "DLeft, DRight")
  subenvs             <- mapM mkEnvForRearr ps
  let envs            =  zipWith (Map.map . foldr (.) id . map (AppE . ConE . contag dleft dright))
                                 (constructLRs (length ps)) subenvs
  return $ Map.unions envs

mkEnvForRearr WildP = return Map.empty

mkEnvForRearr (VarP name) = do
  (_, [dvar]) <- lookupNames [] [ astNameSpace ++ s | s <- ["DVar"] ] (notFoundMsg "DVar")
  return $ Map.singleton (nameBase name) (ConE dvar)

mkEnvForRearr  _    =  fail $ "Pattern not handled yet."





splitDataAndCon:: TH.Exp -> Q (TH.Exp -> TH.Exp ,[TH.Exp])

splitDataAndCon (AppE (ConE name) e2) = do
  lrs <- lookupLRs name
  con <- mkConstrutorFromLRs lrs ETag
  d   <- mkBodyExpForRearr e2
  return (con,[d])

splitDataAndCon (AppE e1 e2) = do
  (c, ds) <- splitDataAndCon e1
  d        <- mkBodyExpForRearr e2
  return (c,ds++[d])

splitDataAndCon _            =  fail $ "Invalid data constructor in lambda body expression"



mkBodyExpForRearr :: TH.Exp -> Q TH.Exp

mkBodyExpForRearr (LitE c) = do
  (_, [econst]) <- lookupNames [] [astNameSpace ++ "EConst"] (notFoundMsg "EConst")
  return $ ConE econst `AppE` (LitE c)

mkBodyExpForRearr (VarE name) =  return $ VarE name

mkBodyExpForRearr (AppE e1 e2) = do
  -- must be constructor applied to arguments (rearrangement expression does not allow general functions)
  -- surface syntax is curried constructor applied to arguments in order; should translate that to uncurried constructor applied to a tuple of arguments
  (_, [eprod]) <- lookupNames [] [astNameSpace ++ "EProd"] (notFoundMsg "EProd")
  (con, ds)   <- splitDataAndCon (AppE e1 e2)
  return $ con (foldr1 (\d1 d2 -> ConE eprod `AppE` d1 `AppE` d2) ds)


mkBodyExpForRearr (ConE name) =  do
  -- must be constructor without argument
  (ConE name') <- [| () |]
  (_, [econst]) <- lookupNames [] [astNameSpace ++ s | s <- ["EConst"] ] (notFoundMsg "EConst")
  if name == name'
  then return $ ConE econst `AppE` (ConE name)
  else mkBodyExpForRearr (AppE (ConE name) (ConE name'))

mkBodyExpForRearr (RecConE name es) = do
  -- reduce to the case for ordinary constructors
  (ConE name') <- [| () |]
  (_, [econst,eprod]) <- lookupNames [] [astNameSpace ++ s | s <- ["EConst","EProd"]] (notFoundMsg "EConst and EProd")
  len <- lookupRecordLength name
  indexs <- mapM (\(n,_) -> lookupRecordField name n) es
  let nes =  map snd es
  mkBodyExpForRearr (foldl (\acc e -> acc `AppE` e) (ConE name) (helper 0 len (zip indexs nes) [] (ConE name')))
  where findInPair [] i  unit = unit
        findInPair ((j,p):xs) i unit | i == j = p
                                     | otherwise = findInPair xs i unit
        helper i n pairs acc unit | i == n = acc
                                  | otherwise = helper (i+1) n pairs (acc ++[(findInPair pairs i unit)]) unit

-- restrict infix op to : for now
mkBodyExpForRearr (InfixE (Just e1) (ConE name) (Just e2)) = do
  (ConE name') <- [| (:) |]
  if name == name'
  then do le <- mkBodyExpForRearr e1
          re <- mkBodyExpForRearr e2
          (_, [ein,eright,eprod]) <- lookupNames [] [astNameSpace ++ s | s <- ["EIn","ERight","EProd"]] (notFoundMsg "EIn, ERight, EProd")
          return $ ConE ein `AppE` (ConE eright `AppE` (ConE eprod `AppE` le `AppE` re))
  else fail $ "only (:) infix operator is allowed in lambda body expression"

mkBodyExpForRearr (ListE [])  = do
  unitt                   <- [| () |]
  (_, [ein,eleft,econst]) <- lookupNames [] [astNameSpace ++ s | s <- ["EIn","ELeft","EConst"]] (notFoundMsg "EIn, ELeft, EConst")
  return $ ConE ein `AppE` (ConE eleft `AppE` (ConE econst `AppE` unitt))
mkBodyExpForRearr (ListE (e:es)) = do
  hexp <- mkBodyExpForRearr e
  rexp <- mkBodyExpForRearr (ListE es)
  (_, [ein,eright,eprod]) <- lookupNames [] [astNameSpace ++ s | s <- ["EIn","ERight","EProd"]] (notFoundMsg "EIn, ERight, EProd")
  return $ ConE ein `AppE` (ConE eright `AppE` (ConE eprod `AppE` hexp `AppE` rexp))

mkBodyExpForRearr (TupE [e])    = mkBodyExpForRearr e
mkBodyExpForRearr (TupE (e:es)) = do
  lexp <- mkBodyExpForRearr e
  rexp <- mkBodyExpForRearr (TupE es)
  (_, [eprod]) <- lookupNames [] [astNameSpace ++ "EProd"] (notFoundMsg "EProd")
  return ((ConE eprod `AppE` lexp) `AppE` rexp)
mkBodyExpForRearr _           = fail $ "Invalid syntax in lambda body expression"






rearr' :: PatTag -> TH.Exp -> [Name] -> Q TH.Exp
rearr' patTag (LamE [p] e) dupnames = do
  let suffixRS = case patTag of {RTag -> "V" ; STag -> "S" ; _ -> ""}
  (_, [edir,rearrc]) <- lookupNames [] [astNameSpace ++ s | s <- ["EDir","Rearr"++suffixRS] ] (notFoundMsg $ "EDir, Rearr"++suffixRS)
  pat <- mkPat p patTag dupnames
  exp <- mkBodyExpForRearr e
  env <- mkEnvForRearr p
  newexp <- rearrangeExp exp (Map.map (ConE edir `AppE`) env)
  return ((ConE rearrc `AppE` pat) `AppE` newexp)

getAllVars :: TH.Exp -> [Name]
getAllVars (LitE c) = []
getAllVars (VarE name) = [name]
getAllVars (AppE e1 e2) = getAllVars e1 ++ getAllVars e2
getAllVars (ConE name) = []
getAllVars (RecConE name es) = concatMap getAllVars (map snd es)
getAllVars (InfixE (Just e1) (ConE name) (Just e2)) = getAllVars e1 ++ getAllVars e2
getAllVars (ListE es) = concatMap getAllVars es
getAllVars (TupE  es) = concatMap getAllVars es
getAllVars  _         =  fail $ "Invalid exp in getAllVars"


rearrV :: Q TH.Exp -> Q TH.Exp
rearrV qlambexp = do lambexp@(LamE _ e) <- qlambexp
                     let varnames = getAllVars e
                     rearr' RTag lambexp (varnames \\ (nub varnames))

rearrS :: Q TH.Exp -> Q TH.Exp
rearrS qlambexp = do lambexp@(LamE _ e) <- qlambexp
                     let varnames = getAllVars e
                     rearr' STag lambexp (varnames \\ (nub varnames))







mkExpFromPat :: TH.Pat -> Q TH.Exp
mkExpFromPat (LitP c) = return (LitE c)
mkExpFromPat (ConP name ps) = do
  es <- mapM mkExpFromPat ps
  return $ foldl (\acc e -> (AppE acc e)) (ConE name) es
mkExpFromPat (RecP name ps) = do
  rs <- mapM mkExpFromPat (map snd ps)
  let es = zip (map fst ps) rs
  return (RecConE name es)
mkExpFromPat (ListP ps) = do
  es <- mapM mkExpFromPat ps
  return (ListE es)
mkExpFromPat (InfixP pl name pr) = do
  epl <- mkExpFromPat pl
  epr <- mkExpFromPat pr
  return (InfixE (Just epl) (ConE name) (Just epr))
mkExpFromPat (TupP ps) = do
  es <- mapM mkExpFromPat ps
  return (TupE es)
mkExpFromPat (VarP name) = return (VarE name)
mkExpFromPat WildP = [| () |]
mkExpFromPat _ = fail $ "pattern not handled in mkExpFromPat"

mkExpFromPat' :: TH.Pat -> Q TH.Exp
mkExpFromPat' (ConP name ps ) = do (_, [replace]) <- lookupNames [] [astNameSpace ++ "Replace"] (notFoundMsg "Replace")
                                   ConP name' [] <- [p| () |]
                                   if name == name' && ps == []
                                   then return (ConE replace)
                                   else  fail $ "rearrSV only supports tuple"
mkExpFromPat' (VarP name) = return (VarE name)
mkExpFromPat' (TupP ps) = do
  (_, [prod]) <- lookupNames [] [ astNameSpace ++ "Prod" ] (notFoundMsg "Prod")
  es <- mapM mkExpFromPat' ps
  return $ foldr1 (\e1 e2 -> ((ConE prod `AppE` e1) `AppE` e2)) es
mkExpFromPat' _ = fail $ "rearrSV only supports tuple"

toProduct :: TH.Exp -> Q TH.Exp
toProduct (AppE e1 e2) = do
  (ConE unitn) <- [| () |]
  (_, [econst,ein,eleft,eright]) <- lookupNames [] [ astNameSpace ++ s | s <- ["EConst","EIn","ELeft", "ERight"] ] (notFoundMsg "EConst, EIn, ELeft, ERight")
  re2 <- toProduct e2
  re1 <- toProduct e1
  if e1 == (ConE eleft) || e1 == (ConE eright) || e1 == (ConE ein)
  then return re2
  else if e1 == (ConE econst)
       then return (AppE e1 (ConE unitn))
       else return (AppE re1 re2)


toProduct other = return other



mkProdPatFromSHelper :: TH.Pat -> Q TH.Pat
mkProdPatFromSHelper (TupP []) = [p| () |]
mkProdPatFromSHelper other     = return other

-- | takes a source pattern and produces a tuple pattern consisting of all the variables in the source pattern
-- 1:s:ss -> (() , (s, ss))
mkProdPatFromS :: TH.Pat -> Q TH.Pat
mkProdPatFromS (LitP c) = [p| () |]
mkProdPatFromS (ConP name ps) = do
  es <- mapM mkProdPatFromS ps
  mkProdPatFromSHelper $ TupP es
mkProdPatFromS (RecP name ps) = do
  rs <- mapM mkProdPatFromS (map snd ps)
  mkProdPatFromSHelper (TupP rs)
mkProdPatFromS (ListP ps) = do
  es <- mapM mkProdPatFromS ps
  mkProdPatFromSHelper (TupP es)
mkProdPatFromS (InfixP pl name pr) = do
  epl <- mkProdPatFromS pl
  epr <- mkProdPatFromS pr
  return (TupP [epl,epr])
mkProdPatFromS (TupP ps) = do
  es <- mapM mkProdPatFromS ps
  mkProdPatFromSHelper (TupP es)
mkProdPatFromS (VarP name) = return (VarP name)
mkProdPatFromS WildP = [p| () |]
mkProdPatFromS _ = fail $ "pattern not handled in mkProdPatFromS"

-- | Example: rearrSV [p| x:xs |] [p| x:xs |] [p| (x,xs) |] [d| x = Replace; xs = rec |]
--   generates a rearrS from the first  pattern and the third pattern
--         and a rearrV from the second pattern and the third pattern
rearrSV :: Q TH.Pat -> Q TH.Pat -> Q TH.Pat -> Q [TH.Dec] -> Q TH.Exp
rearrSV qsp qvp qpp qpd = do
  (_, [edir,rearrs,rearrv]) <- lookupNames [] [astNameSpace ++ s | s <- ["EDir","RearrS","RearrV"] ] (notFoundMsg "EDir, RearrS, RearrV")
  sp <- qsp
  vp <- qvp
  pp <- qpp
  pd <- qpd
  spat <- mkPat sp STag []
  vpat <- mkPat vp RTag []
  commonexp <- mkExpFromPat pp
  commonexp' <- mkBodyExpForRearr commonexp
  commonexp'' <- toProduct commonexp'
  senv <- mkEnvForRearr sp
  sbody <- rearrangeExp commonexp'' (Map.map (ConE edir `AppE`) senv)
  venv <- mkEnvForRearr vp
  vbody <- rearrangeExp commonexp'' (Map.map (ConE edir `AppE`) venv)
  prodexp <- mkExpFromPat' pp
  prodenv <-  mkEnvForUpdate pd
  prodbigul <- rearrangeExp prodexp prodenv
  return $ ((ConE rearrs `AppE` spat) `AppE` sbody) `AppE` (((ConE rearrv `AppE` vpat) `AppE` vbody) `AppE` prodbigul)


update  :: Q TH.Pat -> Q TH.Pat -> Q [TH.Dec] -> Q TH.Exp
update pv ps d = rearrSV ps pv (ps >>= mkProdPatFromS) d

mkEnvForUpdate :: [TH.Dec] -> Q (Map String TH.Exp)
mkEnvForUpdate []                                     = return Map.empty
mkEnvForUpdate ((ValD (VarP name) (NormalB e) _ ):ds) = do
  renv <- mkEnvForUpdate ds
  return $ Map.singleton (nameBase name) e `Map.union` renv
mkEnvForUpdate (_:ds) = fail $ "Invalid syntax in update bindings\n" ++
                               "Please use syntax like x1 = e1 x2 = e2... here"

{-
update :: Q TH.Pat -> Q [TH.Dec] -> Q TH.Exp
update qp qds = do
  (_, [upd]) <- lookupNames [] [astNameSpace ++ "Update"] (notFoundMsg "Update")
  p   <- qp
  ds  <- qds
  pat <- mkPat p UTag
  env <- mkEnvForUpdate ds
  rearrangeExp (ConE upd `AppE` pat) env
-}



patCond :: TH.Pat -> TH.ExpQ
patCond p = do
  (_, [htrue,hfalse]) <- lookupNames [] ["True","False"] (notFoundMsg "True, False")
  var <- newName "x"
  return $ case p of
             TH.WildP -> LamE [VarP var] (ConE htrue)
             _        -> LamE [VarP var] (CaseE (VarE var)
                              [Match p (NormalB (ConE htrue)) [], Match WildP (NormalB (ConE hfalse)) []])

notFoundMsg :: String -> String
notFoundMsg s = "cannot find data constructors " ++ s ++ " from Generic.BiGUL."

withPatTag :: PatTag -> String -> String
withPatTag tag con = show tag ++ con

concatWith :: String -> [String] -> String
concatWith sep [] = ""
concatWith sep (x:xs) = x ++ sep ++ concatWith sep xs


class ExpOrPat a where
  toExp :: a -> TH.ExpQ

instance ExpOrPat (TH.ExpQ) where
  toExp = id

instance ExpOrPat (TH.PatQ) where
  toExp = (>>= patCond)

unaryPatLambdaToPred :: TH.Exp -> TH.ExpQ
unaryPatLambdaToPred p =
  case p of
    LamE [VarP _] _ -> return p
    LamE [pat] body -> do
      var <- newName "x"
      (_, [hfalse]) <-lookupNames [] ["False"] (notFoundMsg "False")
      return (LamE [VarP var]
                (CaseE (VarE var)
                   [Match pat (NormalB body) [],
                    Match WildP (NormalB (ConE hfalse)) []]))
    _ -> return p

binaryPatLambdaToPred :: TH.Exp -> TH.ExpQ
binaryPatLambdaToPred p =
  case p of
    LamE [VarP _, VarP _] _ -> return p
    LamE [spat, vpat] body -> do
      svar <- newName "s"
      vvar <- newName "v"
      (_, [hfalse]) <-lookupNames [] ["False"] (notFoundMsg "False")
      return (LamE [VarP svar, VarP vvar]
                (CaseE (TupE [VarE svar, VarE vvar])
                   [Match (TupP [spat, vpat]) (NormalB body) [],
                    Match WildP (NormalB (ConE hfalse)) []]))
    _ -> return p

-- $(normal [| predicateOnSV |] [| predicateOnS |]) b
--   ~>  (predicateOnSV, Normal b predicateOnS)
normal :: ExpOrPat a => TH.ExpQ -> a -> TH.ExpQ
normal mp mq =
  [| \b -> ($(mp >>= binaryPatLambdaToPred), $(nameNormal) b $(toExp mq >>= unaryPatLambdaToPred)) |]

-- $(normalSV [| predicateOnS |] [| predicateOnV |] [| predicateOnS' |]) b
--   ~>  ((\s v -> predicateOnS s && predicateOnV v), Normal b predicateOnS')
normalSV :: (ExpOrPat a, ExpOrPat b, ExpOrPat c) => a -> b -> c -> TH.ExpQ
normalSV mps mpv mq =
  [|\b -> (\s v -> $(toExp mps) s && $(toExp mpv) v, $(nameNormal) b $(toExp mq >>= unaryPatLambdaToPred)) |]

-- $(adaptive [| predicateOnSV |]) f
--   ~> (predicateOnSV, Adaptive f)
adaptive :: TH.ExpQ -> TH.ExpQ
adaptive mp = [| \f -> ($(mp >>= binaryPatLambdaToPred), $(nameAdaptive) f) |]

-- $(adaptiveSV [| predicateOnS |] [| predicateOnV |]) f
--   ~> ((\s v -> predicateOnS s && predicateOnV v), Adaptive f)
adaptiveSV :: (ExpOrPat a, ExpOrPat b) => a -> b -> TH.ExpQ
adaptiveSV ps pv =
  [| \f -> (\s v -> $(toExp ps >>= unaryPatLambdaToPred) s && $(toExp pv >>= unaryPatLambdaToPred) v, $(nameAdaptive) f) |]

nameAdaptive :: TH.ExpQ
nameAdaptive = lookupNames [] [astNameSpace ++ "Adaptive"] (notFoundMsg "Adaptive") >>= \(_, [badaptive]) -> conE badaptive

nameNormal :: TH.ExpQ
nameNormal = lookupNames [] [astNameSpace ++ "Normal"] (notFoundMsg "Normal") >>= \(_, [bnormal]) -> conE bnormal

