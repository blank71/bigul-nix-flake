-- | The unsafe interpreters, which assume that computation always succeeds and omit all dynamic checking.
--   Use these interpreters only when you have ensured that your 'Generics.BiGUL.BiGUL' program is correct.

module Generics.BiGUL.Interpreter.Unsafe (put, get) where

import Generics.BiGUL
import Generics.BiGUL.PatternMatching


fromRight :: Either a b -> b
fromRight (Right b) = b
fromRight _         = error "fromRight fails"

-- | Unsafe putback semantics of 'Generics.BiGUL.BiGUL' programs.
put :: BiGUL s v -> s -> v -> s
put (Fail str)      s       v       = error ("fail: " ++ str)
put (Skip f)        s       v       = s
put  Replace        s       v       = v
put (l `Prod` r)    (s, s') (v, v') = (put l s v, put r s' v')
put (RearrS p e b)  s       v       = let env = fromRight (deconstruct p s)
                                          m   = eval e env
                                          s'  = put b m v
                                          con = fromRight (uneval p e s' (emptyContainer p))
                                      in  construct p (fromContainerS p env con)
put (RearrV p e b)  s       v       = let v' = fromRight (deconstruct p v)
                                          m  = eval e v'
                                      in  put b s m
put (Dep f b)       s       (v, v') = put b s v
put (Case bs)       s       v       = putCase bs s v
put (l `Compose` r) s       v       = let m  = get l s
                                          m' = put r m v
                                      in  put l s m'

getCaseBranch :: (s -> v -> Bool, CaseBranch s v) -> s -> Maybe v
getCaseBranch (p , Normal b q) s =
  if q s
  then let v = get b s
       in  if p s v then Just v else Nothing
  else Nothing
getCaseBranch (p , Adaptive f) s = Nothing

putCaseWithAdaptation :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v -> (s -> s) -> s
putCaseWithAdaptation (pb@(p, b):bs) s v cont =
  if p s v
  then case b of
         Normal b q -> put b s v
         Adaptive f     -> cont (f s v)
  else putCaseWithAdaptation bs s v cont

putCase :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v -> s
putCase bs s v = putCaseWithAdaptation bs s v (\s' -> putCase bs s' v)

-- | Unsafe get semantics of 'Generics.BiGUL.BiGUL' programs.
get :: BiGUL s v -> s -> v
get (Fail str)      s       = error ("fail: " ++ str)
get (Skip f)        s       = f s
get  Replace        s       = s
get (l `Prod` r)    (s, s') = (get l s, get r s')
get (RearrS p e b)  s       = let env = fromRight (deconstruct p s)
                                  m   = eval e env
                              in  get b m
get (RearrV p e b)  s       = let v'  = get b s
                                  con = fromRight (uneval p e v' (emptyContainer p))
                                  env = fromRight (fromContainerV p con)
                              in  construct p env
get (Dep f b)       s       = let v = get b s in (v, f v)
get (Case bs)       s       = getCase bs s
get (l `Compose` r) s       = let m = get l s in get r m

getCase :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v
getCase (pb@(p, b):bs) s =
  case getCaseBranch pb s of
    Just v  -> v
    Nothing -> getCase bs s
