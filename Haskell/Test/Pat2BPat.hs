{-# LANGUAGE TemplateHaskell #-}

module Pat2BPat where

import Generics.BiGUL
import Generics.BiGUL.AST
import Language.Haskell.TH as TH
import Generics.BiGUL.TH

pat2BPat :: TH.Pat -> Q TH.Exp
pat2BPat p = do
  pat <- mkNPat p
  Just conCaseVB <- lookupValueName "CaseVBranch"
  return $ ConE conCaseVB `AppE` pat
  where
    mkNPat :: TH.Pat -> Q TH.Exp
    mkNPat (LitP lit) = undefined
      --do
      --([pvar] , _) <- lookupNames ["Generics.BiGUL.AST.PVar"] [] "cannot find type constructors from GHC.BiGUL.AST" -- as PVar
      --return $ [ConP pvar]
    -- pattern (_:_) ---> POut (PRight (PProd PVar PVar
    mkNPat (InfixP WildP name WildP) = do
      --rpat <- mkNPat rpat
      (_, [pvar, pprod, pright, pout]) <- lookupNames [] ["Generics.BiGUL.AST." ++ s | s <- ["PVar", "PProd", "PRight", "POut"]] "cannot find type constructors PVar PProd PRight POut from Generics.BiGUL.AST."
      ConE name' <- [| (:) |]
      if name == name'
        then return $ ConE pout `AppE` (ConE pright `AppE` (ConE pprod `AppE` (ConE pvar) `AppE` (ConE pvar)))
        else error $ "type constructors mismatch: " ++ nameBase name ++ " and " ++ nameBase name'
    -- pattern ([]) ---> PConst []
    mkNPat (ConP name []) = do
      (_, [pconst]) <- lookupNames [] ["Generics.BiGUL.AST." ++ s | s <- ["PConst"]] "cannot find type constructors PConst from Generics.BiGUL.AST."
      ConP name' [] <- [p| [] |]
      if name == name'
        then return $ ConE pconst `AppE` (ListE [])
        else error $ "type constructors mismatch: " ++ nameBase name ++ " and " ++ nameBase name'
    -- pattern (x,y,z)) ---> PProd (PLeft)
    mkNPat (TupP [p]) = mkNPat p
    mkNPat (TupP (p:ps)) = do
      lexp <- mkNPat p
      rexp <- mkNPat (TupP ps)
      (_, [pprod, pleft, pright]) <- lookupNames [] ["Generics.BiGUL.AST." ++ s | s <- ["PProd", "PLeft", "PRight"]] "cannot find type constructors PProd PLeft PRight from Generics.BiGUL.AST."
      return ((ConE pprod `AppE` lexp) `AppE` rexp)
    -- pattern (x) ---> PVar
    mkNPat (VarP x) = do
      (_, [pvar]) <- lookupNames [] ["Generics.BiGUL.AST." ++ s | s <- ["PVar"]] "cannot find type constructors PVar from Generics.BiGUL.AST."
      return $ ConE pvar

branch :: Q TH.Pat -> Q TH.Exp
branch quote = quote >>= pat2BPat