{-# LANGUAGE TemplateHaskell #-}

module Pat2BPat(branch, normal',adaptive,normal,mkNPat) where

import Generics.BiGUL
import Generics.BiGUL.AST
import Language.Haskell.TH as TH
import Generics.BiGUL.TH



pat2BPat :: TH.Pat -> Q TH.Exp
pat2BPat p = do
  pat <- mkNPat p "P"
  maybeConCaseVB <- lookupValueName "Generics.BiGUL.AST.CaseVBranch"
  case maybeConCaseVB of
    Nothing -> fail $ "cannot find constructor CaseVBranch"
    Just conCaseVB ->
      return $ ConE conCaseVB `AppE` pat

mkNPat :: TH.Pat -> String -> Q TH.Exp

mkNPat (LitP c) patTag  = do 
  (_, [gconst]) <- lookupNames [] ["Generics.BiGUL.AST." ++ patTag ++ "Const"] "cannot find constructors GConst from Generics.BiGUL.AST."
  return $ ConE gconst `AppE` LitE c




-- user defined datatypes
mkNPat (ConP name ps) patTag = do
      ConP name' [] <- [p| [] |]
      if name == name' && ps == []
      then do 
           (_, [gconst]) <- lookupNames [] ["Generics.BiGUL.AST." ++ patTag ++ "Const"] "cannot find constructors GConst from Generics.BiGUL.AST."
           return $ ConE gconst `AppE` (ListE []) 
      else do
           lrs <- lookupLRs name
           conInEither <- mkConstrutorFromLRs lrs patTag
           pes         <- case ps of
                           [] -> mkNPat (ListP []) patTag 
                           _  -> mkNPat (TupP ps)  patTag
           return $ conInEither pes

-- pattern ([]) ---> PConst []
--mkNPat (ConP name []) patTag = do
--  (_, [gconst]) <- lookupNames [] ["Generics.BiGUL.AST." ++ patTag ++ "Const"] "cannot find constructors GConst from Generics.BiGUL.AST."
--  ConP name' [] <- [p| [] |]
--  if name == name'
--    then return $ ConE gconst `AppE` (ListE [])
--    else fail $ "constructors mismatch: " ++ nameBase name ++ " and " ++ nameBase name'

-- pattern ([_]) or (_ : []) singleton list ---> PIn (PRight (PProd PVar (PConst [])
-- (_ : []) is handled by "InfixP WildP name pats" with pats = ConP GHC.Types.[] []
mkNPat (ListP []) patTag = [p| [] |] >>= flip mkNPat  patTag 
                           
-- pattern ([_, _]). (_ : _ : []) is handled by "InfixP WildP name pats"
mkNPat (ListP (p:xs)) patTag = do
  hexp <- mkNPat p patTag
  rexp <- mkNPat (ListP xs) patTag
  (_, [gelem]) <- lookupNames [] ["Generics.BiGUL.AST." ++ patTag ++ s | s <- ["Elem"]] "cannot find type constructors GElem from Generics.BiGUL.AST."
  return $ (ConE gelem `AppE` hexp) `AppE` rexp

-- pattern (_:_) ---> PIn (PRight (PProd PVar PVar
mkNPat (InfixP pl name pr) patTag = do
  lpat <- mkNPat pl patTag
  rpat <- mkNPat pr patTag
  (_, [gelem]) <- lookupNames [] ["Generics.BiGUL.AST." ++ patTag ++ s | s <- ["Elem"]] "cannot find type constructors GElem from Generics.BiGUL.AST."
  ConE name' <- [| (:) |]
  if name == name'
    then return $ (ConE gelem `AppE` lpat) `AppE` rpat
    else fail $ "constructors mismatch: " ++ nameBase name ++ " and " ++ nameBase name'


-- pattern (x,y,z)) ---> PProd (PLeft)
mkNPat (TupP [p]) patTag = mkNPat p patTag
mkNPat (TupP (p:ps)) patTag = do
  lexp <- mkNPat p patTag
  rexp <- mkNPat (TupP ps) patTag
  (_, [gprod]) <- lookupNames [] ["Generics.BiGUL.AST." ++ patTag ++ s | s <- ["Prod"]] "cannot find constructors GProd from Generics.BiGUL.AST."
  return ((ConE gprod `AppE` lexp) `AppE` rexp)


mkNPat (WildP) "P" = do (_, [pvar]) <- lookupNames [] ["Generics.BiGUL.AST.PVar"]  "cannot find constructors PVar from Generics.BiGUL.AST." 
                        return $ ConE pvar
mkNPat (WildP) "U" = do (_, [uvar, skip]) <- lookupNames [] ["Generics.BiGUL.AST." ++ s | s <- ["UVar", "Skip"]] "cannot find constructors UVar Skip from Generics.BiGUL.AST."
                        return $ ConE uvar `AppE` ConE skip
mkNPat (WildP) "R" = do (_, [rvar]) <- lookupNames [] ["Generics.BiGUL.AST." ++ s | s <- ["RVar"]] "cannot find constructors RVar from Generics.BiGUL.AST."
                        return $ ConE rvar
-- pattern (x) ---> PVar
mkNPat (VarP x) "P" =  fail $ "please do not use variables in Ppatterns. use wildcast(_) instead."
mkNPat (VarP x) "U" =  mkNPat WildP "U"
mkNPat (VarP x) "R" =  mkNPat WildP "R"

mkNPat _ patTag = fail $ "pattern not handled yet."


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