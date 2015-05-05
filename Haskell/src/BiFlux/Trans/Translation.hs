{-# LANGUAGE FlexibleContexts, GADTs, TypeFamilies, ViewPatterns, RankNTypes #-}
module BiFlux.Trans.Translation where

import Lang.AST
import Lang.MonadBiGULError
import Control.Monad
import Control.Monad.Except
import GHC.InOut
import BiFlux.Lang.AST
import BiFlux.DTD.Type as BType
import Text.PrettyPrint
import qualified BiFlux.XPath.HXT.XPathDataTypes as XPath hiding (Name(..),Env(..))
import Text.XML.HaXml.DtdToHaskell.TypeDef hiding (List,Maybe,List1,Any,String,mkAtt)
import Text.XML.HXT.DOM.QualifiedName
import Data.Map



stmt2bigul :: (MonadError Doc m, MonadError' ErrorInfo m') => Stmt -> Type s -> Type v -> TypeEnv -> m (BiGUL m' s v)
-- example 1. update $book in $s/book by ... for view ... where $book/year > 2012
-- example 2. update $book in $s/book by ... for view p[$v1, $v2] in $v where  $v1 := $v2
-- In summarise, whereConds is either a conjunction of where conditons on source or view dependency bindings.
-- whereConds shall be passed into, and decide how to do the translation later.
stmt2bigul (StmtUpd upd whereConds) ts tv typeEnv = update2bigul upd whereConds ts tv typeEnv


update2bigul :: (MonadError Doc m, MonadError' ErrorInfo m') => Upd -> [WhereCond] -> Type s -> Type v -> TypeEnv -> m (BiGUL m' s v)

-- example 1. REPLACE $s/a WITH <b>{$v}</b>
--            SingleReplace Nothing (CPathSlash (CPathVar "$s") (CPathString "a")) (XQElem "b" (XQPath (CPathVar "$v")))
-- Version 0.1: ignore whereConds
-- Computation Steps:
--    Step 1. CPath to UPat
--    Step 2. (Maybe Pat) to UPat
--    Step 3. XQExpr -> Rearr
--    Step 4. Replace
update2bigul (SingleReplace maybePat cpath xqexpr ) whereConds ts tv typeEnv = undefined

-- exist a s', and a UPat m' s' v, we could compute UPat m' s v.
-- not all s' is accetable.
data CUPat m m' s v where
  CUPat :: Type s' -> (Eq v' => Type v' -> UPat m' s' v' -> Expr v v' -> m (UPatExprTuple m' s v)) -> CUPat m m' s v

data UPatExprTuple  m' s v where
  UPatExprTuple :: Eq v'' => Type v'' -> UPat m' s v'' -> Expr v v'' -> UPatExprTuple m' s v


cpath2UPat :: (MonadError Doc m, MonadError' ErrorInfo m') => CPath -> Type s -> Type v -> m (CUPat m m' s v)
cpath2UPat CPathSelf          ts                       tv =
  return $ CUPat ts (\tv' upat' expr' -> return (UPatExprTuple tv' upat' expr'))
cpath2UPat CPathChild         (Data _ subts)           tv =
  return $ CUPat subts (\tv' upat' expr' -> return (UPatExprTuple tv' (UOut upat') expr'))
cpath2UPat CPathAttribute     (Tag (isAtt -> True) subts) tv =
  return $ CUPat subts (\tv' upat' expr' -> return (UPatExprTuple tv' upat' expr'))
cpath2UPat CPathDoS           _                        _  = throwError $ text "CPathDoS not support yet"
cpath2UPat (CPathNodeTest nt) ts                       tv = cpathNodeTest2UPat nt ts tv
--cpath2UPat p@(CPathSlash p1 p2) ts ts' bigul' = cpathslash2UPat p ts ts' bigul'
--cpath2UPat (CPathFilter expr) ts ts' bigul' = undefined
--cpath2UPat (CPathVar    var ) ts ts' bigul' = undefined
--cpath2UPat (CPathString str ) ts ts' bigul' = undefined
--cpath2UPat (CPathBool    b  ) ts ts' bigul' = undefined
--cpath2UPat (CPathSnapshot pat cpath) ts ts' bigul' = undefined
--cpath2UPat (CPathFct    _  _) _  _   _      = throwError $ text "CPath function call unsupported"
--cpath2UPat (CPathIndex  int ) ts ts' bigul' = undefined
--

cpathNodeTest2UPat :: (MonadError Doc m, MonadError' ErrorInfo m') => XPath.NodeTest -> Type s -> Type v -> m (CUPat m m' s v)
cpathNodeTest2UPat (XPath.NameTest qname) (Data (Name dtdName _) subts) tv =
  if qualifiedName qname == dtdName
     then return $ CUPat subts (\tv' upat' expr' -> return (UPatExprTuple tv' (UOut upat') expr'))
     else throwError $ text "NameTest: name not match"
cpathNodeTest2UPat ntqname@(XPath.NameTest qname) (Either ta tb) tv =
  catchError
    ( do
      CUPat ts' bigf <- cpathNodeTest2UPat ntqname ta tv
      return $ CUPat ts' (\tv' upat' expr' -> liftM (\(UPatExprTuple tv'' upat'' expr'') -> UPatExprTuple tv'' (ULeft upat'') expr'') (bigf tv' upat' expr'))
      )
    (\e -> do
      CUPat ts' bigf <- cpathNodeTest2UPat ntqname tb tv
      return $ CUPat ts' (\tv' upat' expr' -> liftM (\(UPatExprTuple tv'' upat'' expr'') -> UPatExprTuple tv'' (URight upat'') expr'') (bigf tv' upat' expr'))
      )
---- catchError :: m a -> (e -> m a) -> m a
-- CUPat :: Type s' -> (Type v' -> UPat m' s' v' -> Expr v v' -> m (UPatExprTuple m' s v)) -> CUPat m m' s v
-- UPatExprTuple ::  Type v'' -> UPat m' s v'' -> Expr v v'' -> UPatExprTuple m' s v
cpathNodeTest2UPat ntqname@(XPath.NameTest qname) (Prod ta tb) tv =
  catchError
    ( do
      CUPat ts' bigf <- cpathNodeTest2UPat ntqname ta tv
      return $ CUPat ts' (\tv' upat' expr' -> liftM (\(UPatExprTuple tv'' upat'' expr'') -> UPatExprTuple (Prod tv'' One) (UProd upat'' (UVar Skip)) (EProd expr'' (EConst ()))) (bigf tv' upat' expr'))
      )
    (\e -> do
      CUPat ts' bigf <- cpathNodeTest2UPat ntqname tb tv
      return $ CUPat ts' (\tv' upat' expr' -> liftM (\(UPatExprTuple tv'' upat'' expr'') -> UPatExprTuple (Prod One tv'') (UProd (UVar Skip) upat'') (EProd (EConst ()) expr'')) (bigf tv' upat' expr'))
      )
--cpathNodeTest2UPat (PI str) _ = throwError $ text "PI not supported"
--cpathNodeTest2UPat (TypeTest XPNode) ts = undefined
--cpathNodeTest2UPat (TypeTest XPCommentNode) ts = undefined
--cpathNodeTest2UPat (TypeTest XPPINode) ts = undefined
--cpathNodeTest2UPat (TypeTest XPTextNode) ts = undefined
--cpathNodeTest2UPat (TypeTest XPString) ts = undefined
