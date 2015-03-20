module DynamicallyChecked.ViewCase (S V : Set) where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Lens

open import Level using (Level)
open import Function
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin
open import Data.List
open import Data.Vec hiding (_>>=_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


mapPar-with-index : {l m : Level} {A : Set l} {B : Set m} {n : ℕ} → (Fin n → A → B) → Vec A n → List B
mapPar-with-index f []       = []
mapPar-with-index f (x ∷ xs) = f zero x ∷ mapPar-with-index (f ∘ suc) xs

put : {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → S → V → Par S
put ls lsel s v = lsel v >>= λ i → Lens.put (lookup i ls) s v

get-and-check : {n : ℕ} → (V → Par (Fin n)) → S → Fin n → (S ⇆ V) → Par V
get-and-check lsel s i l = Lens.get l s >>= λ v → lsel v >>= λ j → assert (i ==ᶠ j) then return v

get : {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → S → Par V
get ls lsel s = ⊕ (mapPar-with-index (get-and-check lsel s) ls)

PutGet : {n : ℕ} (ls : Vec (S ⇆ V) n) (lsel : V → Par (Fin n)) {s s' : S} {v : V} →
         put ls lsel s v ↦ s' → get ls lsel s' ↦ v
PutGet ls lsel put↦ = {!!}

caseV-lens : {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → S ⇆ V
caseV-lens ls lsel = record { put = put ls lsel; get = get ls lsel; PutGet = PutGet ls lsel; GetPut = {!!} }
