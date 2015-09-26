{-# LANGUAGE TemplateHaskell #-}

module Pat2BPat where

import Generics.BiGUL
import Generics.BiGUL.AST
import Language.Haskell.TH as TH
import Generics.BiGUL.TH

pat2BPat :: TH.Pat -> Q TH.Exp
pat2BPat p = do
  pat <- mkNPat p
  maybeConCaseVB <- lookupValueName "Generics.BiGUL.AST.CaseVBranch"
  case maybeConCaseVB of
    Nothing -> error $ "cannot find constructor CaseVBranch"
    Just conCaseVB ->
      return $ ConE conCaseVB `AppE` pat
  where
    mkNPat :: TH.Pat -> Q TH.Exp
    -- pattern ([]) ---> PConst []
    mkNPat (ConP name []) = do
      (_, [pconst]) <- lookupNames [] ["Generics.BiGUL.AST.PConst"] "cannot find constructors PConst from Generics.BiGUL.AST."
      ConP name' [] <- [p| [] |]
      if name == name'
        then return $ ConE pconst `AppE` (ListE [])
        else error $ "constructors mismatch: " ++ nameBase name ++ " and " ++ nameBase name'

    -- pattern ([_]) or (_ : []) singleton list ---> POut (PRight (PProd PVar (PConst [])
    -- (_ : []) is handled by "InfixP WildP name pats" with pats = ConP GHC.Types.[] []
    mkNPat (ListP [WildP]) = [p| _:[] |] >>= mkNPat

    -- pattern ([_, _]). (_ : _ : []) is handled by "InfixP WildP name pats"
    mkNPat (ListP (WildP:xs)) = do
      rexp <- mkNPat (ListP xs)
      (_, [pvar, pprod, pright, pout]) <- lookupNames [] ["Generics.BiGUL.AST." ++ s | s <- ["PVar", "PProd", "PRight", "POut"]] "cannot find type constructors PVar PProd PRight POut from Generics.BiGUL.AST."
      return $ ConE pout `AppE` (ConE pright `AppE` (ConE pprod `AppE` (ConE pvar) `AppE` rexp))

    -- pattern (_:_) ---> POut (PRight (PProd PVar PVar
    mkNPat (InfixP WildP name pats) =
      case pats of
        VarP _ -> error $ "cannot use variables in list patterns. use wildcast instead"
        _      -> do
          rpat <- mkNPat pats
          (_, [pvar, pprod, pright, pout]) <- lookupNames [] ["Generics.BiGUL.AST." ++ s | s <- ["PVar", "PProd", "PRight", "POut"]] "cannot find type constructors PVar PProd PRight POut from Generics.BiGUL.AST."
          ConE name' <- [| (:) |]
          if name == name'
            then return $ ConE pout `AppE` (ConE pright `AppE` (ConE pprod `AppE` (ConE pvar) `AppE` rpat))
            else error $ "constructors mismatch: " ++ nameBase name ++ " and " ++ nameBase name'
    mkNPat (WildP) = lookupNames [] ["Generics.BiGUL.AST.PVar"]  "cannot find constructors PVar from Generics.BiGUL.AST." >>= \(_, [pvar]) -> return $ ConE pvar

    -- pattern (x,y,z)) ---> PProd (PLeft)
    mkNPat (TupP [p]) = mkNPat p
    mkNPat (TupP (p:ps)) = do
      lexp <- mkNPat p
      rexp <- mkNPat (TupP ps)
      (_, [pprod, pleft, pright]) <- lookupNames [] ["Generics.BiGUL.AST." ++ s | s <- ["PProd", "PLeft", "PRight"]] "cannot find constructors PProd PLeft PRight from Generics.BiGUL.AST."
      return ((ConE pprod `AppE` lexp) `AppE` rexp)

    -- pattern (x) ---> PVar
    mkNPat (VarP x) = do
      (_, [pvar]) <- lookupNames [] ["Generics.BiGUL.AST.PVar"] "cannot find constructors PVar from Generics.BiGUL.AST."
      return $ ConE pvar


branch :: Q TH.Pat -> Q TH.Exp
branch quote = quote >>= pat2BPat

      --(_, [pvar, pprod, pright, pout]) <- lookupNames [] ["Generics.BiGUL.AST." ++ s | s <- ["PVar", "PProd", "PRight", "POut"]] "cannot find type constructors PVar PProd PRight POut from Generics.BiGUL.AST."
      --ConE name' <- [| (:) |]
      --if name == name'
      --  then return $ ConE pout `AppE` (ConE pright `AppE` (ConE pprod `AppE` (ConE pvar) `AppE` (ConE pvar)))
      --  else error $ "type constructors mismatch: " ++ nameBase name ++ " and " ++ nameBase name'