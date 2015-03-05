module DynamicallyChecked.Partiality where

open import Function
open import Data.Unit
import Data.Maybe as Maybe; open Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality


infix 5 _↪_

_↪_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
ma ↪ f = maybe f nothing ma

infix 5 _↢_

_↢_ : {A B C : Set} → (B → Maybe C) → (A → Maybe B) → (A → Maybe C)
(f ↢ g) a = g a ↪ f

infix 4 _≡ᴶ_

_≡ᴶ_ : {A : Set} → Maybe A → A → Set
mx ≡ᴶ y = mx ≡ just y

fmap-equals-just : {A B : Set} {f : A → B} (mx : Maybe A) {y : B} →
                   Maybe.map f mx ≡ᴶ y → Σ[ x ∈ A ] mx ≡ᴶ x × f x ≡ y
fmap-equals-just nothing  ()
fmap-equals-just (just x) refl = x , refl , refl

bind-equals-just : {A B : Set} {f : A → Maybe B} (mx : Maybe A) {y : B} →
                   mx ↪ f ≡ᴶ y → Σ[ x ∈ A ] mx ≡ᴶ x × f x ≡ᴶ y
bind-equals-just nothing  ()
bind-equals-just (just x) eq = x , refl , eq

reduce-bind : {A B : Set} {mx : Maybe A} {x : A} {f : A → Maybe B} → mx ≡ᴶ x → mx ↪ f ≡ f x
reduce-bind {mx = nothing} ()
reduce-bind {mx = just x } refl = refl

reduce-bind-eq : {A B : Set} {mx : Maybe A} {x : A} {f : A → Maybe B} {y : Maybe B} → mx ≡ᴶ x → mx ↪ f ≡ y → f x ≡ y
reduce-bind-eq {mx = nothing} ()   eq
reduce-bind-eq {mx = just x } refl eq = eq

reduce-fmap : {A B : Set} {f : A → B} {mx : Maybe A} {x : A} → mx ≡ᴶ x → Maybe.map f mx ≡ᴶ f x
reduce-fmap {mx = nothing} ()
reduce-fmap {mx = just x } refl = refl

record Iso (A B : Set) : Set where
  field
    to   : A → Maybe B
    from : B → Maybe A
    to-from-inverse : (x : A) {y : B} → to x ≡ᴶ y → from y ≡ᴶ x
    from-to-inverse : (y : B) {x : A} → from y ≡ᴶ x → to x ≡ᴶ y

infix 0 _≅_

_≅_ : Set → Set → Set
_≅_ = Iso

id-iso : {A : Set} → A ≅ A
id-iso = record
  { to   = just
  ; from = just
  ; to-from-inverse = λ { _ refl → refl }
  ; from-to-inverse = λ { _ refl → refl } }

sym-iso : {A B : Set} → A ≅ B → B ≅ A
sym-iso iso = record
  { to   = Iso.from iso
  ; from = Iso.to   iso
  ; to-from-inverse = Iso.from-to-inverse iso
  ; from-to-inverse = Iso.to-from-inverse iso }

trans-iso : {A B C : Set} → A ≅ B → B ≅ C → A ≅ C
trans-iso {A} {B} {C} iso-l iso-r = record
  { to   = Iso.to iso-r ↢ Iso.to iso-l
  ; from = Iso.from iso-l ↢ Iso.from iso-r
  ; from-to-inverse = from-to-inverse
  ; to-from-inverse = to-from-inverse }
  where
    from-to-inverse : (c : C) {a : A} → (Iso.from iso-l ↢ Iso.from iso-r) c ≡ᴶ a → (Iso.to iso-r ↢ Iso.to iso-l) a ≡ᴶ c
    from-to-inverse c {a} eq with bind-equals-just (Iso.from iso-r c) eq
    from-to-inverse c {a} _  | b , from-r-eq , from-l-eq =
      begin
        Iso.to iso-l a ↪ Iso.to iso-r
          ≡⟨ reduce-bind (Iso.from-to-inverse iso-l b from-l-eq) ⟩
        Iso.to iso-r b
          ≡⟨ Iso.from-to-inverse iso-r c from-r-eq ⟩
        just c
      ∎
      where open ≡-Reasoning
    to-from-inverse : (a : A) {c : C} → (Iso.to iso-r ↢ Iso.to iso-l) a ≡ᴶ c → (Iso.from iso-l ↢ Iso.from iso-r) c ≡ᴶ a
    to-from-inverse a {c} eq with bind-equals-just (Iso.to iso-l a) eq
    to-from-inverse a {c} _  | b , to-l-eq , to-r-eq =
      begin
        Iso.from iso-r c ↪ Iso.from iso-l
          ≡⟨ reduce-bind (Iso.to-from-inverse iso-r b to-r-eq) ⟩
        Iso.from iso-l b
          ≡⟨ Iso.to-from-inverse iso-l a to-l-eq ⟩
        just a
      ∎
      where open ≡-Reasoning

prod-unit-iso : {A : Set} → A ≅ A × ⊤
prod-unit-iso = record
  { to   = λ x → just (x , tt)
  ; from = λ { (x , _) → just x }
  ; from-to-inverse = λ { _ refl → refl }
  ; to-from-inverse = λ { _ refl → refl } }

prod-comm-iso : {A B : Set} → A × B ≅ B × A
prod-comm-iso = record
  { to   = just ∘ swap
  ; from = just ∘ swap
  ; from-to-inverse = λ { _ refl → refl }
  ; to-from-inverse = λ { _ refl → refl } }
