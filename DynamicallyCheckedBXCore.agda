module DynamicallyCheckedBXCore where

open import Level using (Level)
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.Nat
open import Data.Fin
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


postulate DONE : {ℓ : Level} {A : Set ℓ} → A

infix 5 _↪_

_↪_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
ma ↪ f = maybe f nothing ma

infix 5 _↢_

_↢_ : {A B C : Set} → (B → Maybe C) → (A → Maybe B) → (A → Maybe C)
(f ↢ g) a = g a ↪ f

infix 4 _≡ᴶ_

_≡ᴶ_ : {A : Set} → Maybe A → A → Set
mx ≡ᴶ y = mx ≡ just y

record Lens (S V : Set) : Set where
  field
    put : S → V → Maybe S
    get : S → Maybe V
    PutGet : (s : S) (v : V) {s' : S} → put s v ≡ᴶ s' → get s' ≡ᴶ v
    GetPut : (s : S) {v : V} → get s ≡ᴶ v → put s v ≡ᴶ s

infix 1 _⇆_

_⇆_ : Set → Set → Set
_⇆_ = Lens

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

record Iso (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from-to-inverse : (x : A) → from (to x) ≡ x
    to-from-inverse : (y : B) → to (from y) ≡ y

infix 1 _≅_

_≅_ : Set → Set → Set
_≅_ = Iso

iso-lens : {A B : Set} → A ≅ B → A ⇆ B
iso-lens iso = record
  { put = const (just ∘ Iso.from iso)
  ; get = just ∘ Iso.to iso
  ; PutGet = λ { s v refl → DONE {- cong just (Iso.to-from-inverse iso v) -} }
  ; GetPut = λ { s   refl → DONE {- cong just (Iso.from-to-inverse iso s) -} } }

bind-equals-just : {A B : Set} {f : A → Maybe B} (mx : Maybe A) {y : B} →
                   mx ↪ f ≡ᴶ y → Σ[ x ∈ A ] mx ≡ᴶ x × f x ≡ᴶ y
bind-equals-just nothing  ()
bind-equals-just (just x) eq = x , refl , eq

reduce-bind : {A B : Set} {mx : Maybe A} {x : A} {f : A → Maybe B} → mx ≡ᴶ x → mx ↪ f ≡ f x
reduce-bind {mx = nothing} ()
reduce-bind {mx = just x } refl = refl

focus-lens : {S F S' V : Set} → S ⇆ F × S' → F ⇆ V → S ⇆ V
focus-lens {S} {F} {S'} {V} outer-lens inner-lens = record { put = put; get = get; PutGet = PutGet; GetPut = GetPut }
  where
    put : S → V → Maybe S
    put s v = Lens.get outer-lens s ↪ λ { (focus , residual) →
              Lens.put inner-lens focus v ↪ λ focus' →
              Lens.put outer-lens s (focus' , residual) }

    get : S → Maybe V
    get = (Lens.get inner-lens ∘ proj₁) ↢ Lens.get outer-lens

    PutGet : (s : S) (v : V) {s' : S} → put s v ≡ᴶ s' → get s' ≡ᴶ v
    PutGet s v      eq with bind-equals-just (Lens.get outer-lens s) eq
    PutGet s v      _  | (focus , residual) , outer-get-eq , eq with bind-equals-just (Lens.put inner-lens focus v) eq
    PutGet s v {s'} _  | (focus , residual) , outer-get-eq , _  | focus' , inner-put-eq , outer-put-eq =
      begin
        get s'
          ≡⟨ refl ⟩
        Lens.get outer-lens s' ↪ Lens.get inner-lens ∘ proj₁
          ≡⟨ reduce-bind (Lens.PutGet outer-lens s (focus' , residual) outer-put-eq) ⟩
        Lens.get inner-lens focus'
          ≡⟨ Lens.PutGet inner-lens focus v inner-put-eq ⟩
        just v
      ∎
      where open ≡-Reasoning

    GetPut : (s : S) {v : V} → get s ≡ᴶ v → put s v ≡ᴶ s
    GetPut s {v} eq with bind-equals-just (Lens.get outer-lens s) eq
    GetPut s {v} _  | (focus , residual) , outer-get-eq , inner-get-eq =
      begin
        put s v
          ≡⟨ reduce-bind outer-get-eq ⟩
        Lens.put inner-lens focus v ↪ (λ focus' → Lens.put outer-lens s (focus' , residual))
          ≡⟨ reduce-bind (Lens.GetPut inner-lens focus inner-get-eq) ⟩
        Lens.put outer-lens s (focus , residual)
          ≡⟨ Lens.GetPut outer-lens s outer-get-eq ⟩
        just s
      ∎
      where open ≡-Reasoning

data U (n : ℕ) : Set₁ where
  var  : (i : Fin n) → U n
  zero : U n
  one  : U n
  k    : (A : Set) → U n
  _⊕_  : (F G : U n) → U n
  _⊗_  : (F G : U n) → U n
  list : (F : U n) → U n

⟦_⟧ : {n : ℕ} → U n → (Fin n → Set) → Set
⟦ var  i ⟧ Xs = Xs i
⟦ zero   ⟧ Xs = ⊥
⟦ one    ⟧ Xs = ⊤
⟦ k A    ⟧ Xs = A
⟦ F ⊕ G  ⟧ Xs = ⟦ F ⟧ Xs ⊎ ⟦ G ⟧ Xs
⟦ F ⊗ G  ⟧ Xs = ⟦ F ⟧ Xs × ⟦ G ⟧ Xs
⟦ list F ⟧ Xs = List (⟦ F ⟧ Xs)

Functor : ℕ → Set₁
Functor n = Fin n → U n

data μ {n : ℕ} (F : Functor n) : Fin n → Set where
  con : {i : Fin n} → ⟦ F i ⟧ (μ F) → μ F i

prod-unit-iso : {A : Set} → A ≅ A × ⊤
prod-unit-iso = record
  { to   = λ x → x , tt
  ; from = λ { (x , _) → x }
  ; from-to-inverse = λ _ → refl
  ; to-from-inverse = λ _ → refl }

trans-iso : {A B C : Set} → A ≅ B → B ≅ C → A ≅ C
trans-iso iso-l iso-r = record
  { to   = Iso.to iso-r ∘ Iso.to iso-l
  ; from = Iso.from iso-l ∘ Iso.from iso-r
  ; from-to-inverse =
      flip trans (Iso.from-to-inverse iso-l _) ∘ cong (Iso.from iso-l) ∘ Iso.from-to-inverse iso-r ∘ Iso.to iso-l
  ; to-from-inverse =
      flip trans (Iso.to-from-inverse iso-r _) ∘ cong (Iso.to iso-r) ∘ Iso.to-from-inverse iso-l ∘ Iso.from iso-r }

child : {n : ℕ} {i : Fin n} (F : Functor n) → μ F i ⇆ ⟦ F i ⟧ (μ F) × ⊤
child F = iso-lens (trans-iso (record { to   = λ { (con xs) → xs }
                                      ; from = con
                                      ; from-to-inverse = λ { (con xs) → refl }
                                      ; to-from-inverse = λ x → refl })
                              prod-unit-iso)

id-lens : {A : Set} → A ⇆ A
id-lens = record
  { put = λ _ a → just a
  ; get = just
  ; PutGet = λ { _ _ refl → refl }
  ; GetPut = λ { _ refl → refl } }

prod-comm-iso : {A B : Set} → A × B ≅ B × A
prod-comm-iso = record
  { to   = swap
  ; from = swap
  ; from-to-inverse = λ _ → refl
  ; to-from-inverse = λ _ → refl }

outl : {A B : Set} → A × B ⇆ A × B
outl = id-lens

outr : {A B : Set} → A × B ⇆ B × A
outr = iso-lens prod-comm-iso

list-elem : {A : Set} → List A ⇆ A × (List A × List A)
list-elem = record
  { put = {!!}
  ; get = {!!}
  ; PutGet = {!!}
  ; GetPut = {!!} }


-- equal-or-not : {n : ℕ} (i j : Fin n) → Dec (i ≡ j)
-- equal-or-not zero    zero    = yes refl
-- equal-or-not zero    (suc _) = no (λ ())
-- equal-or-not (suc _) zero    = no (λ ())
-- equal-or-not (suc i) (suc j) with equal-or-not i j
-- equal-or-not (suc i) (suc j) | yes eq = yes (cong suc eq)
-- equal-or-not (suc i) (suc j) | no neq = no (neq ∘ cong-pred)
--   where
--     cong-pred : {n : ℕ} {i j : Fin n} → (Fin (suc n) ∋ suc i) ≡ suc j → i ≡ j
--     cong-pred refl = refl

