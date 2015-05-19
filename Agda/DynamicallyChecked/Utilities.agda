module DynamicallyChecked.Utilities where

open import Level using (Level)
open import Function
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.List
open import Data.Fin
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


record ⊤ {l : Level} : Set l where
  constructor tt
  
data ⊥ {l : Level} : Set l where

infix 5 _≟ᶠ_

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

≟ᶠ-reflexive : {n : ℕ} (i : Fin n) → i ≟ᶠ i ≡ yes refl
≟ᶠ-reflexive zero    = refl
≟ᶠ-reflexive (suc i) with i ≟ᶠ i
≟ᶠ-reflexive (suc i) | yes refl = refl
≟ᶠ-reflexive (suc i) | no  i≢i  with i≢i refl
≟ᶠ-reflexive (suc i) | no  i≢i  | ()

infix 5 _==ᶠ_

_==ᶠ_ : {n : ℕ} → Fin n → Fin n → Bool
i ==ᶠ j with i ≟ᶠ j
i ==ᶠ j | yes _ = true
i ==ᶠ j | no  _ = false

eqFin : {n : ℕ} {i j : Fin n} → i ==ᶠ j ≡ true → i ≡ j
eqFin {i = i} {j} _  with i ≟ᶠ j
eqFin {i = i} {j} _  | yes eq = eq
eqFin {i = i} {j} () | no _

==ᶠ-reflexive : {n : ℕ} {i j : Fin n} → i ≡ j → i ==ᶠ j ≡ true
==ᶠ-reflexive {i = i} {j} eq with i ≟ᶠ j
==ᶠ-reflexive {i = i} {j} eq | yes _   = refl
==ᶠ-reflexive {i = i} {j} eq | no  i≢j with i≢j eq
==ᶠ-reflexive {i = i} {j} eq | no  i≢j | ()

pred' : {n : ℕ} → Fin (suc n) → Maybe (Fin n)
pred' zero    = nothing  
pred' (suc n) = just n

revcat : {l : Level} {A : Set l} → List A → List A → List A
revcat []       ys = ys
revcat (x ∷ xs) ys = revcat xs (x ∷ ys)
