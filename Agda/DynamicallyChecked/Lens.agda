module DynamicallyChecked.Lens where

open import DynamicallyChecked.Partiality

open import Function
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality


record Lens (S V : Set) : Set₁ where
  field
    put : S → V → Par S
    get : S → Par V
    PutGet : {s : S} {v : V} {s' : S} → put s v ↦ s' → get s' ↦ v
    GetPut : {s : S} {v : V} → get s ↦ v → put s v ↦ s

infix 1 _⇆_

_⇆_ : Set → Set → Set₁
_⇆_ = Lens

infixr 3 _↔_

_↔_ : {A B C : Set} → A ⇆ B → B ⇆ C → A ⇆ C
_↔_ {A} {B} {C} l r = record
  { put = λ a c → Lens.get l a >>= λ b → Lens.put r b c >>= Lens.put l a
  ; get = Lens.get r <=< Lens.get l
  ; PutGet = λ { (get-l-a↦b >>= put-r-b↦b' >>= put-l-a-b'↦a') → Lens.PutGet l put-l-a-b'↦a' >>= Lens.PutGet r put-r-b↦b' }
  ; GetPut = λ { (get-l-a↦b >>= get-r-b↦c) → get-l-a↦b >>= Lens.GetPut r get-r-b↦c >>= Lens.GetPut l get-l-a↦b } }

iso-lens : {A B : Set} → A ≅ B → A ⇆ B
iso-lens iso = record
  { put = const (Iso.from iso)
  ; get = Iso.to iso
  ; PutGet = Iso.from-to-inverse iso
  ; GetPut = Iso.to-from-inverse iso }

fail-lens : {S V : Set} → S ⇆ V
fail-lens = record
  { put = λ s v → fail
  ; get = λ s → fail
  ; PutGet = λ ()
  ; GetPut = λ () }

skip-lens : {S : Set} → S ⇆ ⊤
skip-lens = record
  { put = λ s _ → return s
  ; get = λ s → return tt
  ; PutGet = λ { {._} (return refl) → return refl }
  ; GetPut = λ _ → return refl }
