module Generics.BiGUL.Interpreter.Unsafe (put, get) where

import Generics.BiGUL
import Generics.BiGUL.PatternMatching


fromRight :: Either a b -> b
fromRight (Right b) = b
fromRight _         = error "fromRight fails"

put :: BiGUL s v -> s -> v -> s
put (Fail err)              s       v       = error ("fail: " ++ err)
put (Skip f)                s       v       = s
put Replace                 s       v       = v
put (Prod bigul bigul')     (s, s') (v, v') = (put bigul s v, put bigul' s' v')
put (RearrS pat expr bigul) s       v       = let env = fromRight (deconstruct pat s)
                                                  m   = eval expr env
                                                  s'  = put bigul m v
                                                  con = fromRight (uneval pat expr s' (emptyContainer pat))
                                              in  construct pat (fromContainerS pat env con)
put (RearrV pat expr bigul) s       v       = let v' = fromRight (deconstruct pat v)
                                                  m  = eval expr v'
                                              in  put bigul s m
put (Dep f b)               s       (v, v') = put b s v
put (Case branches)         s       v       = putCase branches s v
put (Compose bigul bigul')  s       v       = let m  = get bigul s
                                                  m' = put bigul' m v
                                              in  put bigul s m'

getCaseBranch :: (s -> v -> Bool, CaseBranch s v) -> s -> Maybe v
getCaseBranch (p , Normal bigul q) s =
  if q s
  then let v = get bigul s
       in  if p s v then Just v else Nothing
  else Nothing
getCaseBranch (p , Adaptive f)     s = Nothing

putCaseWithAdaptation :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v -> (s -> s) -> s
putCaseWithAdaptation (pb@(p, b):bs) s v cont =
  if p s v
  then case b of
         Normal bigul q -> put bigul s v
         Adaptive f     -> cont (f s v)
  else putCaseWithAdaptation bs s v cont

putCase :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v -> s
putCase bs s v = putCaseWithAdaptation bs s v (\s' -> putCase bs s' v)

get :: BiGUL s v -> s -> v
get (Fail err)              s       = error ("fail: " ++ err)
get (Skip f)                s       = f s
get (RearrS pat expr bigul) s       = let env = fromRight (deconstruct pat s)
                                          m   = eval expr env
                                      in  get bigul m
get (RearrV pat expr bigul) s       = let v'  = get bigul s
                                          con = fromRight (uneval pat expr v' (emptyContainer pat))
                                          env = fromRight (fromContainerV pat con)
                                      in  construct pat env
get (Dep f b)               s       = let v = get b s
                                      in  (v, f v)
get (Case branches)         s       = getCase branches s
get (Compose bigul bigul')  s       = let m = get bigul s
                                      in  get bigul' m

getCase :: [(s -> v -> Bool, CaseBranch s v)] -> s -> v
getCase (pb@(p, b):bs) s =
  case getCaseBranch pb s of
    Just v  -> v
    Nothing -> getCase bs s
