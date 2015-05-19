open import DynamicallyChecked.Universe
open import Data.Nat

module DynamicallyChecked.BiGUL {n : ℕ} (F : Functor n) where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.SourceUpdate

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


data BiGUL : U n → U n → Set₁ where
  fail    : {S V : U n} → BiGUL S V
  skip    : {S : U n} → BiGUL S one
  replace : {S : U n} → BiGUL S S
  update  : {S : U n} → (pat : Pattern F S) (lenses : PatLenses pat) → BiGUL S (PatLensesViews pat lenses)
