module DynamicallyChecked.ViewCase where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Lens

open import Function
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (_>>=_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


put : {S V : Set} {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → S → V → Par S
put ls lsel s v = lsel v >>= λ i → Lens.put (lookup i ls) s v

get : {S V : Set} {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → S → Par V
get []       lsel s = fail
get (l ∷ ls) lsel s = catch (Lens.get l s >>= λ v → lsel v >>= λ i → assert i ==ᶠ zero then return v)
                            (get ls (embed ∘ pred' <=< lsel) s)

PutGet : {S V : Set} {n : ℕ} (ls : Vec (S ⇆ V) n) (lsel : V → Par (Fin n)) {s s' : S} {v : V} →
         put ls lsel s v ↦ s' → get ls lsel s' ↦ v
PutGet [] lsel (_>>=_ {x = ()} _ _)
PutGet (l ∷ ls) lsel (_>>=_ {x = zero } lsel↦ put↦) = catch-fst (Lens.PutGet l put↦ >>= lsel↦ >>= assert refl then return refl)
PutGet (l ∷ ls) lsel (_>>=_ {x = suc i} lsel↦ put↦) = catch-snd {!!} {!!}


caseV-lens : {S V : Set} {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → S ⇆ V
caseV-lens ls lsel = {!!}
