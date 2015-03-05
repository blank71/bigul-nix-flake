module DynamicallyChecked.Utilities where

open import Function
open import Data.Nat
open import Data.Fin
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

_≟ᶠ_ : {n : ℕ} (i j : Fin n) → Dec (i ≡ j)
zero  ≟ᶠ zero  = yes refl
zero  ≟ᶠ suc _ = no (λ ())
suc _ ≟ᶠ zero  = no (λ ())
suc i ≟ᶠ suc j with i ≟ᶠ j
suc i ≟ᶠ suc j | yes eq = yes (cong suc eq)
suc i ≟ᶠ suc j | no neq = no (neq ∘ cong-pred)
  where
    cong-pred : {n : ℕ} {i j : Fin n} → (Fin (suc n) ∋ suc i) ≡ suc j → i ≡ j
    cong-pred refl = refl
