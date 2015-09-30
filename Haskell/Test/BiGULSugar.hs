{-# LANGUAGE TemplateHaskell #-}

module BiGULSugar(branch, normal',adaptive,normal,rearr,update) where

import Generics.BiGUL
import Generics.BiGUL.AST
import Language.Haskell.TH as TH
import Generics.BiGUL.TH
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad

astNameSpace :: String
astNameSpace = "Generics.BiGUL.AST."

mkPat :: TH.Pat -> PatTag -> Q TH.Exp

mkPat (LitP c) patTag  = do
  (_, [gconst]) <- lookupNames [] [astNameSpace ++ show patTag ++ "Const"] (notFoundMsg $ show patTag ++ "Const")
  return $ ConE gconst `AppE` LitE c


-- user defined datatypes && empty list
mkPat (ConP name ps) patTag = do
  ConP name' [] <- [p| [] |]
  if name == name' && ps == []
  then do
       unitt                   <- [| () |]
       (_, [gin,gleft,gconst]) <- lookupNames [] [astNameSpace ++ show patTag ++ s | s <- ["In","Left","Const"]] (notFoundMsg $ (concatWith " ". map (withPatTag patTag)) ["In","Left","Const"])
       return $ ConE gin `AppE` (ConE gleft `AppE` (ConE gconst `AppE` unitt))
  else do
       lrs <- lookupLRs name
       conInEither <- mkConstrutorFromLRs lrs patTag
       pes         <- case ps of
                       [] -> mkPat (ListP []) patTag
                       _  -> mkPat (TupP ps)  patTag
       return $ conInEither pes


mkPat (ListP []) patTag = [p| [] |] >>= flip mkPat  patTag

mkPat (ListP (p:xs)) patTag = do
  hexp <- mkPat p patTag
  rexp <- mkPat (ListP xs) patTag
  (_, [gin,gright,gprod]) <- lookupNames [] [astNameSpace ++ show patTag ++ s | s <- ["In","Right","Prod"]] (notFoundMsg $ (concatWith " ". map (withPatTag patTag)) ["In","Right","Prod"])
  return $ ConE gin `AppE` (ConE gright `AppE` (ConE gprod `AppE` hexp `AppE` rexp))

mkPat (InfixP pl name pr) patTag = do
  ConE name' <- [| (:) |]
  if name == name'
  then do lpat <- mkPat pl patTag
          rpat <- mkPat pr patTag
          (_, [gin,gright,gprod]) <- lookupNames [] [astNameSpace ++ show patTag ++ s | s <- ["In","Right","Prod"]] (notFoundMsg $ (concatWith " ". map (withPatTag patTag)) ["In","Right","Prod"])
          return $ ConE gin `AppE` (ConE gright `AppE` (ConE gprod `AppE` lpat `AppE` rpat))
  else fail $ "constructors mismatch: " ++ nameBase name ++ " and " ++ nameBase name'


mkPat (TupP [p]) patTag = mkPat p patTag
mkPat (TupP (p:ps)) patTag = do
  lexp <- mkPat p patTag
  rexp <- mkPat (TupP ps) patTag
  (_, [gprod]) <- lookupNames [] [astNameSpace ++ show patTag ++ s | s <- ["Prod"]] (notFoundMsg "Prod")
  return ((ConE gprod `AppE` lexp) `AppE` rexp)


mkPat (WildP) PTag = do
  (_, [pvar])       <- lookupNames [] [astNameSpace ++ "PVar"]  (notFoundMsg "PVar")
  return $ ConE pvar
mkPat (WildP) UTag = do
  (_, [uvar, skip]) <- lookupNames [] [astNameSpace ++ s | s <- ["UVar", "Skip"]] (notFoundMsg "UVar, Skip")
  return $ ConE uvar `AppE` ConE skip
mkPat (WildP) RTag = do
  (_, [rvar])       <- lookupNames [] [astNameSpace ++ "RVar"] (notFoundMsg "RVar")
  return $ ConE rvar
mkPat (VarP name) PTag =  fail $ "please do not use variables in Ppatterns. use wildcast(_) instead."
mkPat (VarP name) UTag =  do
  (_, [uvar])       <- lookupNames [] [astNameSpace ++ "UVar"] (notFoundMsg "UVar")
  return $ ConE uvar `AppE` VarE name

mkPat (VarP name) RTag =  mkPat WildP RTag

mkPat _ patTag = fail $ "pattern not handled yet."


-- rearrange all (VarE name) with env, generalized version
rearrangeExp :: Exp -> Map String Exp -> Q Exp
rearrangeExp (VarE name) env  =
  case Map.lookup (nameBase name) env of
    Just val -> return val
    Nothing  -> fail $ "cannot find name in env"
rearrangeExp (AppE e1 e2) env = liftM2 AppE (rearrangeExp e1 env) (rearrangeExp e2 env)
rearrangeExp (ConE name) env  = return $ ConE name
rearrangeExp _           env  = fail $ "invalid representation of bigul program in TemplateHaskell ast"



mkEnvForRearr :: TH.Pat -> Q (Map String Exp)
mkEnvForRearr (LitP c) = return Map.empty

-- empty list is ok , mkEnvForRearr return Q Map.empty for it
mkEnvForRearr (ConP name ps) = mkEnvForRearr (ListP ps)

mkEnvForRearr (ListP ps)     = do
  (_, [dleft,dright]) <- lookupNames [] [ astNameSpace ++ s | s <- ["DLeft", "DRight"] ] (notFoundMsg "DLeft, DRight")
  subenvs             <- mapM mkEnvForRearr ps
  let envs            =  zipWith (Map.map . foldr (.) id . map (AppE . ConE . contag dleft dright))
                                 (constructLRs (length ps)) subenvs
  return $ Map.unions envs

mkEnvForRearr (InfixP pl name pr) = do
  (_, [dleft,dright]) <- lookupNames [] [ astNameSpace ++ s | s <- ["DLeft", "DRight"] ] (notFoundMsg "DLeft, DRight")
  lenv <- mkEnvForRearr pl
  renv <- mkEnvForRearr pr
  return $ Map.map (ConE dleft `AppE`) lenv `Map.union`
          Map.map (ConE dright `AppE`) renv

mkEnvForRearr (TupP ps) = mkEnvForRearr (ListP ps)

mkEnvForRearr WildP = return Map.empty

mkEnvForRearr (VarP name) = do
  (_, [dvar]) <- lookupNames [] [ astNameSpace ++ s | s <- ["DVar"] ] (notFoundMsg "DVar")
  return $ Map.singleton (nameBase name) (ConE dvar)

mkBodyExpForRearr :: TH.Exp -> Q TH.Exp
mkBodyExpForRearr (VarE name) =  return $ VarE name

-- a little trick here, in order to extract conInEither from Exp -> Exp type
mkBodyExpForRearr (ConE name) =  do
  (ConE name') <- [| () |]
  if name == name'
  then do (_, [econst]) <- lookupNames [] [astNameSpace ++ s | s <- ["EConst"] ] (notFoundMsg "EConst")
          return $ ConE econst `AppE` (ConE name)
  else do lrs <- lookupLRs name
          conWithAppE <- mkConstrutorFromLRs lrs RTag
          let (AppE conInEither _) = conWithAppE (ConE name)
          return $ conInEither

-- restrict infix op to : for now
mkBodyExpForRearr (InfixE (Just e1) (ConE name) (Just e2)) = do
  (ConE name') <- [| (:) |]
  if name == name'
  then do le <- mkBodyExpForRearr e1
          re <- mkBodyExpForRearr e2
          (_, [ein,eright,eprod]) <- lookupNames [] [astNameSpace ++ s | s <- ["EIn","ERight","EProd"]] (notFoundMsg "EIn, ERight, EProd")
          return $ ConE ein `AppE` (ConE eright `AppE` (ConE eprod `AppE` le `AppE` re))
  else fail $ "only (:) infix operator is allowed in rearrange body"

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
mkBodyExpForRearr _           = fail $ "invalid syntax in rearrange body"


rearr' :: TH.Exp -> Q TH.Exp
rearr' (LamE [p] e) = do
  (_, [edir,rearrc]) <- lookupNames [] [astNameSpace ++ s | s <- ["EDir","Rearr"] ] (notFoundMsg "EDir, Rearr")
  pat <- mkPat p RTag
  exp <- mkBodyExpForRearr e
  env <- mkEnvForRearr p
  newexp <- rearrangeExp exp (Map.map (ConE edir `AppE`) env)
  return ((ConE rearrc `AppE` pat) `AppE` newexp)

rearr :: Q TH.Exp -> Q TH.Exp
rearr = (rearr' =<<)


mkEnvForUpdate :: [TH.Dec] -> Q (Map String TH.Exp)
mkEnvForUpdate []                                     = return Map.empty
mkEnvForUpdate ((ValD (VarP name) (NormalB e) _ ):ds) = do
  renv <- mkEnvForUpdate ds
  return $ Map.singleton (nameBase name) e `Map.union` renv
mkEnvForUpdate (_:ds) = fail $ "invalid syntax in update bindings"


update :: Q TH.Pat -> Q [TH.Dec] -> Q TH.Exp
update qp qds = do
  (_, [upd]) <- lookupNames [] [astNameSpace ++ "Update"] (notFoundMsg "Update")
  p   <- qp
  ds  <- qds
  pat <- mkPat p UTag
  env <- mkEnvForUpdate ds
  rearrangeExp (ConE upd `AppE` pat) env

branch :: Q TH.Pat -> Q TH.Exp
branch mp = do
  p <- mp
  pat <- mkPat p PTag
  (_, [caseVBranch]) <- lookupNames [] [astNameSpace ++ "CaseVBranch"] (notFoundMsg "CaseVBranch")
  return $ ConE caseVBranch `AppE` pat


normal' :: Q TH.Exp -> Q TH.Exp
normal' me  = do
  e <- me
  case e of
    (LamE pat exp) -> do
      exp' <- [| return $ $(return exp) |]
      let mexp = return (LamE pat exp')
      let a = [| ( $([| $(mexp) |]), Normal) |]
      [| \update -> fmap ($ update) $(a) |]
    _  -> do
      let a = [| ( $([| return . $(me) |]), Normal) |]
      [| \update -> fmap ($ update) $(a) |]


normal :: Q TH.Pat -> Q TH.Exp
normal pat = let a = [| ( $([|\s -> return $ case s of $(pat) -> True; _ -> False|]) , Normal ) |]
             in      [| \update -> fmap ($ update) $(a)   |]

adaptive :: Q TH.Pat -> Q TH.Exp
adaptive pat = let a = [| ($([|\s -> return $ case s of $(pat) -> True; _ -> False|]), Adaptive) |]
               in      [| \adapt -> fmap ($ adapt) $(a) |]

--
notFoundMsg :: String -> String
notFoundMsg s = "cannot find data constructors " ++ s ++ " from Generic.BiGUL.AST"

withPatTag :: PatTag -> String -> String
withPatTag tag con = show tag ++ con

concatWith :: String -> [String] -> String
concatWith sep [] = ""
concatWith sep (x:xs) = x ++ sep ++ concatWith sep xs