module DynamicallyChecked.ViewCase (S V : Set) where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Lens

open import Function
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.Fin
open import Data.List
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


get-and-check : {n : ℕ} → (S ⇆ V) → (V → Par (Fin (suc n))) → S → Par V
get-and-check l lsel s = Lens.get l s >>= λ v → lsel v >>= λ i → assert (i ==ᶠ zero) then return v

restrict : {n : ℕ} → (V → Par (Fin (suc n))) → V → Par (Fin n)
restrict f = embed ∘ pred' <=< f

put-branch-check : {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → Fin n → S → Par S
put-branch-check ls       lsel zero    s = return s
put-branch-check (l ∷ ls) lsel (suc i) s = catch (get-and-check l lsel s) (const fail) (put-branch-check ls (restrict lsel) i s)

put : {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → S → V → Par S
put ls lsel s v = lsel v >>= λ i → Lens.put (lookup i ls) s v >>= put-branch-check ls lsel i

get : {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → S → Par V
get []       lsel s = fail
get (l ∷ ls) lsel s = catch (get-and-check l lsel s) return (get ls (restrict lsel) s)

PutGet : {n : ℕ} (ls : Vec (S ⇆ V) n) (lsel : V → Par (Fin n)) {s s' : S} {v : V} →
         put ls lsel s v ↦ s' → get ls lsel s' ↦ v
PutGet []       lsel (_>>=_ {x = ()} _ _)
PutGet (l ∷ ls) lsel (_>>=_ {x = zero } lsel↦ (put↦ >>= return refl)) = {!!}
PutGet (l ∷ ls) lsel (_>>=_ {x = suc i} lsel↦ (put↦ >>= comp)) = {!!}

caseV-lens : {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → S ⇆ V
caseV-lens ls lsel = record { put = put ls lsel; get = get ls lsel; PutGet = PutGet ls lsel; GetPut = {!!} }
