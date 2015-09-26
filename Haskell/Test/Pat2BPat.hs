{-# LANGUAGE TemplateHaskell #-}

module Pat2BPat(branch, normal',adaptive,normal) where

import Generics.BiGUL
import Generics.BiGUL.AST
import Language.Haskell.TH as TH
import Generics.BiGUL.TH

pat2BPat :: TH.Pat -> Q TH.Exp
pat2BPat p = do
  pat <- mkNPat p
  maybeConCaseVB <- lookupValueName "Generics.BiGUL.AST.CaseVBranch"
  case maybeConCaseVB of
    Nothing -> fail $ "cannot find constructor CaseVBranch"
    Just conCaseVB ->
      return $ ConE conCaseVB `AppE` pat

mkNPat :: TH.Pat -> Q TH.Exp
-- pattern ([]) ---> PConst []
mkNPat (ConP name []) = do
  (_, [pconst]) <- lookupNames [] ["Generics.BiGUL.AST.PConst"] "cannot find constructors PConst from Generics.BiGUL.AST."
  ConP name' [] <- [p| [] |]
  if name == name'
    then return $ ConE pconst `AppE` (ListE [])
    else fail $ "constructors mismatch: " ++ nameBase name ++ " and " ++ nameBase name'

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
    VarP _ -> fail $ "cannot use variables in list patterns. use wildcast instead"
    _      -> do
      rpat <- mkNPat pats
      (_, [pvar, pprod, pright, pout]) <- lookupNames [] ["Generics.BiGUL.AST." ++ s | s <- ["PVar", "PProd", "PRight", "POut"]] "cannot find type constructors PVar PProd PRight POut from Generics.BiGUL.AST."
      ConE name' <- [| (:) |]
      if name == name'
        then return $ ConE pout `AppE` (ConE pright `AppE` (ConE pprod `AppE` (ConE pvar) `AppE` rpat))
        else fail $ "constructors mismatch: " ++ nameBase name ++ " and " ++ nameBase name'
mkNPat (WildP) = lookupNames [] ["Generics.BiGUL.AST.PVar"]  "cannot find constructors PVar from Generics.BiGUL.AST." >>= \(_, [pvar]) -> return $ ConE pvar

-- pattern (x,y,z)) ---> PProd (PLeft)
mkNPat (TupP [p]) = mkNPat p
mkNPat (TupP (p:ps)) = do
  lexp <- mkNPat p
  rexp <- mkNPat (TupP ps)
  (_, [pprod, pleft, pright]) <- lookupNames [] ["Generics.BiGUL.AST." ++ s | s <- ["PProd", "PLeft", "PRight"]] "cannot find constructors PProd PLeft PRight from Generics.BiGUL.AST."
  return ((ConE pprod `AppE` lexp) `AppE` rexp)

-- pattern (x) ---> PVar
mkNPat (VarP x) = fail $ "please do not use variables in patterns. use wildcast(_) instead."
mkNPat _ = fail $ "pattern not handled yet."


branch :: Q TH.Pat -> Q TH.Exp
branch quote = quote >>= pat2BPat


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







--(Update (UElem (UVar Replace) (UVar (uLefts a0))))

--($(update [p| x : xs |])
          --[d| x  = Replace
          --    xs = uLefts a0 |])



--(Update (UElem (UVar Skip)
--             (UVar (uLefts a0))
--       )
--)
-- $(update [p| _ : xs |] [d| xs = uLefts a0 |]))