module Generics.BiGUL.Lib where

import Generics.BiGUL
import Generics.BiGUL.TH


skip :: Eq v => v -> BiGUL s v
skip v = Skip (const v)

(==>) :: (a -> b) -> a -> b
(==>) = ($)

infixr 0 ==>

emb :: Eq v => (s -> v) -> (s -> v -> s) -> BiGUL s v
emb g p = Case
  [ $(normal [| \s v -> g s == v |] [p| _ |])
    ==> Skip g
  , $(adaptive [| \s v -> {- g s /= v -} True |])
    ==> p
  ]

