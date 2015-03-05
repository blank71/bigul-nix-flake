module DynamicallyChecked.Lens where

open import DynamicallyChecked.Partiality

open import Function
open import Data.Unit
open import Data.Maybe
open import Relation.Binary.PropositionalEquality


record Lens (S V : Set) : Set where
  field
    put : S → V → Maybe S
    get : S → Maybe V
    PutGet : (s : S) (v : V) {s' : S} → put s v ≡ᴶ s' → get s' ≡ᴶ v
    GetPut : (s : S) {v : V} → get s ≡ᴶ v → put s v ≡ᴶ s

infix 1 _⇆_

_⇆_ : Set → Set → Set
_⇆_ = Lens

iso-lens : {A B : Set} → A ≅ B → A ⇆ B
iso-lens iso = record
  { put = const (Iso.from iso)
  ; get = Iso.to iso
  ; PutGet = λ s v eq → Iso.from-to-inverse iso v eq
  ; GetPut = λ s eq → Iso.to-from-inverse iso s eq }

fail : {S V : Set} → S ⇆ V
fail = record
  { put = λ s v → nothing
  ; get = λ s → nothing
  ; PutGet = λ s v ()
  ; GetPut = λ s () }

skip : {S : Set} → S ⇆ ⊤
skip = record
  { put = λ s _ → just s
  ; get = λ s → just tt
  ; PutGet = λ { s _ refl → refl }
  ; GetPut = λ s _ → refl }
