module DynamicallyChecked.Lens where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Utilities

open import Function
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
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

_≼ᴾ_ : {A : Set} → Par A → Par A → Set₁
mx ≼ᴾ my = ∀ {a} → mx ↦ a → my ↦ a

_≈ᴾ_ : {A : Set} → Par A → Par A → Set₁
mx ≈ᴾ my = (mx ≼ᴾ my) × (my ≼ᴾ mx)

uniqueness-lemma : {S V : Set} (l l' : S ⇆ V) {s : S} {v : V} →
                   ({s : S} {v : V} → Lens.put l s v ≼ᴾ Lens.put l' s v) → Lens.get l s ↦ v → Lens.get l' s ↦ v
uniqueness-lemma l l' put-≼ = Lens.PutGet l' ∘ put-≼ ∘ Lens.GetPut l

uniqueness : {S V : Set} (l l' : S ⇆ V) →
             ({s : S} {v : V} → Lens.put l s v ≈ᴾ Lens.put l' s v) → {s : S} → Lens.get l s ≈ᴾ Lens.get l' s
uniqueness l l' put-eq = uniqueness-lemma l l' (proj₁ put-eq) , uniqueness-lemma l' l (proj₂ put-eq)

iso-lens : {A B : Set} → A ≅ B → A ⇆ B
iso-lens iso = record
  { put = const (Iso.from iso)
  ; get = Iso.to iso
  ; PutGet = Iso.from-to-inverse iso
  ; GetPut = Iso.to-from-inverse iso }

skip-lens : {S : Set} → S ⇆ ⊤
skip-lens = record
  { put = λ s _ → return s
  ; get = λ s → return tt
  ; PutGet = λ { {._} (return refl) → return refl }
  ; GetPut = λ _ → return refl }

infixr 3 _↔_ _↕_ _◁_ _▷_

_↔_ : {A B C : Set} → A ⇆ B → B ⇆ C → A ⇆ C
l ↔ r = record
  { put = λ a c → Lens.get l a >>= λ b → Lens.put r b c >>= Lens.put l a
  ; get = Lens.get r <=< Lens.get l
  ; PutGet = λ { (get-l-a↦b >>= put-r-b↦b' >>= put-l-a-b'↦a') → Lens.PutGet l put-l-a-b'↦a' >>= Lens.PutGet r put-r-b↦b' }
  ; GetPut = λ { (get-l-a↦b >>= get-r-b↦c) → get-l-a↦b >>= Lens.GetPut r get-r-b↦c >>= Lens.GetPut l get-l-a↦b } }

_◁_ : {A B C : Set} → A ⇆ B → B ≅ C → A ⇆ C
l ◁ iso = record
  { put = λ a c → Iso.from iso c >>= Lens.put l a
  ; get = Iso.to iso <=< Lens.get l
  ; PutGet = λ { (from-v↦v' >>= put-s-v'↦s') → Lens.PutGet l put-s-v'↦s' >>= Iso.from-to-inverse iso from-v↦v' }
  ; GetPut = λ { (get-s↦v >>= to-v↦v') → Iso.to-from-inverse iso to-v↦v' >>= Lens.GetPut l get-s↦v } } 

_▷_ : {A B C : Set} → A ≅ B → B ⇆ C → A ⇆ C
iso ▷ l = iso-lens iso ↔ l

_↕_ : {A B C D : Set} → A ⇆ B → C ⇆ D → A × C ⇆ B × D
l ↕ r = record
  { put = λ { (a , c) (b , d) → liftPar₂ _,_ (Lens.put l a b) (Lens.put r c d) }
  ; get = λ { (a , c) → liftPar₂ _,_ (Lens.get l a) (Lens.get r c) }
  ; PutGet = λ { (put-l↦ >>= put-r↦ >>= return refl) → Lens.PutGet l put-l↦ >>= Lens.PutGet r put-r↦ >>= return refl }
  ; GetPut = λ { (get-l↦ >>= get-r↦ >>= return refl) → Lens.GetPut l get-l↦ >>= Lens.GetPut r get-r↦ >>= return refl } }

dependency-lens : {A B C : Set} → A ⇆ B → (A → B → C) → Decidable (_≡_ {A = C}) → A ⇆ B × C
dependency-lens {A} {B} {C} l f dec = record
  { put    = put
  ; get    = get
  ; PutGet = PutGet
  ; GetPut = GetPut }
  where
    put-aux : A → B → C → Par A
    put-aux a b c with dec (f a b) c
    put-aux a b c | yes _ = return a
    put-aux a b c | no  _ = fail

    put : A → B × C → Par A
    put a (b , c) = Lens.put l a b >>= λ a' → put-aux a' b c

    get : A → Par (B × C)
    get a = Lens.get l a >>= (λ b → return (b , f a b))

    PutGet : {a : A} {bc : B × C} {a' : A} → put a bc ↦ a' → get a' ↦ bc
    PutGet {a} {b , c } (_>>=_ {x = a''} put↦ put-aux↦) with dec (f a'' b) c
    PutGet {a} {b , ._} (put↦ >>= (return refl)) | yes refl = Lens.PutGet l put↦ >>= return refl
    PutGet {a} {b , c } (put↦ >>= ()           ) | no  _

    GetPut-aux : {a : A} {b : B} → put-aux a b (f a b) ↦ a
    GetPut-aux {a} {b} with dec (f a b) (f a b)
    GetPut-aux {a} {b} | yes _   = return refl
    GetPut-aux {a} {b} | no  neq with neq refl
    GetPut-aux {a} {b} | no  neq | ()

    GetPut : {a : A} {bc : B × C} → get a ↦ bc → put a bc ↦ a
    GetPut {a} {b , ._} (get↦ >>= return refl) = Lens.GetPut l get↦ >>= GetPut-aux
