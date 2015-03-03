module DynamicallyCheckedCore where

open import Partiality
open import MutuallyRecursiveUniverse

open import Level using (Level)
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
import Data.Maybe as Maybe
open Maybe
open import Data.Nat
open import Data.Fin
open import Data.List
open import Relation.Nullary
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

--------
-- source focusing

focus-lens : {S F S' V : Set} → S ≅ F × S' → F ⇆ V → S ⇆ V
focus-lens {S} {F} {S'} {V} iso lens = record { put = put; get = get; PutGet = PutGet; GetPut = GetPut }
  where
    put : S → V → Maybe S
    put s v = Iso.to iso s ↪ λ { (focus , residual) →
              Lens.put lens focus v ↪ λ focus' →
              Iso.from iso (focus' , residual) }
    get : S → Maybe V
    get = (Lens.get lens ∘ proj₁) ↢ Iso.to iso
    PutGet : (s : S) (v : V) {s' : S} → put s v ≡ᴶ s' → get s' ≡ᴶ v
    PutGet s v      eq with bind-equals-just (Iso.to iso s) eq
    PutGet s v      _  | (focus , residual) , to-eq , eq with bind-equals-just (Lens.put lens focus v) eq
    PutGet s v {s'} _  | (focus , residual) , to-eq , _  | focus' , put-eq , from-eq =
      begin
        get s'
          ≡⟨ refl ⟩
        Iso.to iso s' ↪ Lens.get lens ∘ proj₁
          ≡⟨ reduce-bind (Iso.from-to-inverse iso (focus' , residual) from-eq) ⟩
        Lens.get lens focus'
          ≡⟨ Lens.PutGet lens focus v put-eq ⟩
        just v
      ∎
      where open ≡-Reasoning
    GetPut : (s : S) {v : V} → get s ≡ᴶ v → put s v ≡ᴶ s
    GetPut s {v} eq with bind-equals-just (Iso.to iso s) eq
    GetPut s {v} _  | (focus , residual) , to-eq , get-eq =
      begin
        put s v
          ≡⟨ reduce-bind to-eq ⟩
        Lens.put lens focus v ↪ (λ focus' → Iso.from iso (focus' , residual))
          ≡⟨ reduce-bind (Lens.GetPut lens focus get-eq) ⟩
        Iso.from iso (focus , residual)
          ≡⟨ Iso.to-from-inverse iso s to-eq ⟩
        just s
      ∎
      where open ≡-Reasoning

-- path components

child : {n : ℕ} {i : Fin n} (F : Functor n) → μ F i ≅ ⟦ F i ⟧ (μ F) × ⊤
child F = trans-iso (record { to   = λ { (con xs) → just xs }
                            ; from = λ xs → just (con xs)
                            ; to-from-inverse = λ { (con xs) refl → refl }
                            ; from-to-inverse = λ { xs refl → refl } })
                    prod-unit-iso

nth-elem : {A : Set} → ℕ → List A ≅ A × (List A × List A)
nth-elem {A} n = record
  { to   = split n
  ; from = λ { (x , ys , zs) → unsplit n x ys zs }
  ; from-to-inverse = λ { (x , ys , zs) → split-unsplit n x ys zs }
  ; to-from-inverse = λ ws eq → unsplit-split n ws eq }
  where
    split : ℕ → List A → Maybe (A × (List A × List A))
    split n       []       = nothing
    split zero    (x ∷ xs) = just (x , [] , xs)
    split (suc n) (x ∷ xs) = Maybe.map (λ { (y , zs , ws) → y , x ∷ zs , ws }) (split n xs)
    unsplit : ℕ → A → List A → List A → Maybe (List A)
    unsplit zero    x []       zs = just (x ∷ zs)
    unsplit (suc n) x []       zs = nothing
    unsplit zero    x (y ∷ ys) zs = nothing
    unsplit (suc n) x (y ∷ ys) zs = Maybe.map (_∷_ y) (unsplit n x ys zs)
    split-unsplit : (n : ℕ) (x : A) (ys zs : List A) {ws : List A} →
                    unsplit n x ys zs ≡ just ws → split n ws ≡ just (x , ys , zs)
    split-unsplit zero    x []       zs refl = refl
    split-unsplit (suc n) x []       zs ()
    split-unsplit zero    x (y ∷ ys) zs ()
    split-unsplit (suc n) x (y ∷ ys) zs eq with fmap-equals-just (unsplit n x ys zs) eq
    split-unsplit (suc n) x (y ∷ ys) zs _  | ws , unsplit-eq , refl = reduce-fmap (split-unsplit n x ys zs unsplit-eq)
    unsplit-split : (n : ℕ) (ws : List A) {x : A} {ys zs : List A} →
                    split n ws ≡ just (x , ys , zs) → unsplit n x ys zs ≡ just ws
    unsplit-split n       []       ()
    unsplit-split zero    (w ∷ ws) refl = refl
    unsplit-split (suc n) (w ∷ ws) eq with fmap-equals-just (split n ws) eq
    unsplit-split (suc n) (w ∷ ws) _  | (x , ys , zs) , split-eq , refl = cong (Maybe.map (_∷_ w))
                                                                               (unsplit-split n ws split-eq)
