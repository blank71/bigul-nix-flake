module THAST where

import Generics.BiGUL
import Language.Haskell.TH as TH
import Data.Map (Map)
import qualified Data.Map as Map

rearrPatTH :: TH.Pat -> Q (Exp, Map Name Exp)
rearrPatTH (VarP name)   = do Just conRVar <- lookupValueName "RVar"
                              Just conDVar <- lookupValueName "DVar"
                              return (ConE conRVar, Map.singleton name (ConE conDVar))
rearrPatTH (TupP [p])    = rearrPatTH p
rearrPatTH (TupP (p:ps)) = do (lexp, lenv) <- rearrPatTH p
                              (rexp, renv) <- rearrPatTH (TupP ps)
                              Just conRProd <- lookupValueName "RProd"
                              Just conDLeft <- lookupValueName "DLeft"
                              Just conDRight <- lookupValueName "DRight"
                              return ((ConE conRProd `AppE` lexp) `AppE` rexp,
                                      Map.map (ConE conDLeft `AppE`) lenv `Map.union`
                                      Map.map (ConE conDRight `AppE`) renv)


rearrExprTH :: Exp -> Map Name Exp -> Q Exp
rearrExprTH (VarE name)   env =
  case Map.lookup name env of
    Just path -> do Just conEDir <- lookupValueName "EDir"
                    return (ConE conEDir `AppE` path)
rearrExprTH (ConE name)   env = do Just conEConst <- lookupValueName "EConst"
                                   return (ConE conEConst `AppE` ConE name)
rearrExprTH (TupE [e])    env = rearrExprTH e env
rearrExprTH (TupE (e:es)) env = do e0 <- rearrExprTH e env
                                   e1 <- rearrExprTH (TupE es) env
                                   Just conEProd <- lookupValueName "EProd"
                                   return ((ConE conEProd `AppE` e0) `AppE` e1)

rearrTH :: Exp -> Q Exp
rearrTH (LamE [p] e) = do (pat, env) <- rearrPatTH p
                          expr <- rearrExprTH e env
                          Just conRearr <- lookupValueName "Rearr"
                          return ((ConE conRearr `AppE` pat) `AppE` expr)

