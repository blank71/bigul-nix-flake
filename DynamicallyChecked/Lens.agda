module DynamicallyChecked.Lens where

open import DynamicallyChecked.Partiality

open import Function
open import Data.Unit
open import Data.Maybe
open import Data.Product
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

infixr 3 _↔_

_↔_ : {A B C : Set} → A ⇆ B → B ⇆ C → A ⇆ C
_↔_ {A} {B} {C} l r = record { put = put; get = get; PutGet = PutGet; GetPut = GetPut }
  where
    put : A → C → Maybe A
    put a c = Lens.get l a ↪ λ b → Lens.put r b c ↪ Lens.put l a
    get : A → Maybe C
    get = Lens.get r ↢ Lens.get l
    PutGet : (a : A) (c : C) {a' : A} → put a c ≡ᴶ a' → get a' ≡ᴶ c
    PutGet a c {a'} eq with bind-equals-just (Lens.get l a) eq
    PutGet a c {a'} _  | b , get-l-a≡ᴶb , eq with bind-equals-just (Lens.put r b c) eq
    PutGet a c {a'} _  | b , get-l-a≡ᴶb , _ | b' , put-r-b-c≡ᴶb' , put-l-a-b'≡ᴶa' =
      begin
        get a'
          ≡⟨ refl ⟩
        Lens.get l a' ↪ Lens.get r
          ≡⟨ reduce-bind (Lens.PutGet l a b' put-l-a-b'≡ᴶa') ⟩
        Lens.get r b'
          ≡⟨ Lens.PutGet r b c put-r-b-c≡ᴶb' ⟩
        just c
      ∎
      where open ≡-Reasoning
    GetPut : (a : A) {c : C} → get a ≡ᴶ c → put a c ≡ᴶ a
    GetPut a {c} eq with bind-equals-just (Lens.get l a) eq
    GetPut a {c} _  | b , get-l-a≡ᴶb , get-r-b≡ᴶc =
      begin
        put a c
          ≡⟨ reduce-bind get-l-a≡ᴶb ⟩
        Lens.put r b c ↪ Lens.put l a
          ≡⟨ reduce-bind (Lens.GetPut r b get-r-b≡ᴶc) ⟩
        Lens.put l a b
          ≡⟨ Lens.GetPut l a get-l-a≡ᴶb ⟩
        just a
      ∎
      where open ≡-Reasoning

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
