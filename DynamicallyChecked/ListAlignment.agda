module DynamicallyChecked.ListAlignment where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Function
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality


singleton-list-iso : {A : Set} → List A ≅ A
singleton-list-iso = record
  { to   = λ { []          → nothing
             ; (x ∷ [])    → just x
             ; (_ ∷ _ ∷ _) → nothing }
  ; from = λ x → just (x ∷ [])
  ; to-from-inverse = λ { []          ()
                        ; (x ∷ [])    refl → refl
                        ; (_ ∷ _ ∷ _) () }
  ; from-to-inverse = λ { x refl → refl } }

singleton-list-lens : {S V : Set} → S ⇆ V → List S ⇆ List V
singleton-list-lens l = iso-lens singleton-list-iso ↔ l ↔ iso-lens (sym-iso singleton-list-iso)
