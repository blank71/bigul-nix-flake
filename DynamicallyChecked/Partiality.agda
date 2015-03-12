module DynamicallyChecked.Partiality where

open import Function
open import Data.Unit
open import Data.Bool
import Data.Maybe as Maybe; open Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality


data Par : Set → Set₁ where
  fail         : {A   : Set} → Par A
  return       : {A   : Set} → A → Par A
  _>>=_        : {A B : Set} → Par A → (A → Par B) → Par B
  assert_then_ : {A   : Set} → Bool → Par A → Par A
  embed        : {A   : Set} → Maybe A → Par A

runPar : {A : Set} → Par A → Maybe A
runPar fail       = nothing
runPar (return x) = just x
runPar (mx >>= f) with runPar mx
runPar (mx >>= f) | just x  = runPar (f x)
runPar (mx >>= f) | nothing = nothing
runPar (assert true  then mx) = runPar mx
runPar (assert false then mx) = nothing
runPar (embed mx) = mx

_>>_ : {A B : Set} → Par A → Par B → Par B
mx >> my = mx >>= const my

infixr 8 _<=<_

_<=<_ : {A B C : Set} → (B → Par C) → (A → Par B) → (A → Par C)
(f <=< g) x = g x >>= f

liftM : {A B : Set} → (A → B) → Par A → Par B
liftM f mx = mx >>= λ x → return (f x)

liftM₂ : {A B C : Set} → (A → B → C) → Par A → Par B → Par C
liftM₂ f mx my = mx >>= λ x → my >>= λ y → return (f x y)

infixr 1 _>>=_
infix 1 assert_then_

data CompSeq : {A : Set} → Par A → A → Set₁ where
  return       : {A : Set} {x x' : A} → x ≡ x' → CompSeq (return x) x'
  _>>=_        : {A B : Set} {x : A} {mx : Par A} {f : A → Par B} {y : B} →
                 CompSeq mx x → CompSeq (f x) y → CompSeq (mx >>= f) y
  embed        : {A : Set} {mx : Maybe A} {x : A} → mx ≡ just x → CompSeq (embed mx) x
  assert_then_ : {A : Set} {b : Bool} {mx : Par A} {x : A} → b ≡ true → CompSeq mx x → CompSeq (assert b then mx) x

_↦_ : {A : Set} → Par A → A → Set₁
_↦_ = CompSeq

toCompSeq : {A : Set} {mx : Par A} {x : A} → runPar mx ≡ just x → CompSeq mx x
toCompSeq {mx = fail                } ()
toCompSeq {mx = return x            } refl = return refl
toCompSeq {mx = mx >>= f            } eq   with runPar mx | inspect runPar mx
toCompSeq {mx = mx >>= f            } eq   | just x  | [ runPar-mx≡just-x ] = toCompSeq runPar-mx≡just-x >>= toCompSeq eq
toCompSeq {mx = mx >>= f            } ()   | nothing | _
toCompSeq {mx = embed ._            } refl = embed refl
toCompSeq {mx = assert true  then mx} eq   = assert refl then toCompSeq eq
toCompSeq {mx = assert false then mx} ()  

fromCompSeq : {A : Set} {mx : Par A} {x : A} → CompSeq mx x → runPar mx ≡ just x
fromCompSeq (return refl               ) = refl
fromCompSeq (_>>=_ {mx = mx} comp comp') with runPar mx | inspect runPar mx
fromCompSeq (_>>=_ {mx = mx} comp comp') | just x' | [ eq ] with trans (sym eq) (fromCompSeq comp)
fromCompSeq (_>>=_ {mx = mx} comp comp') | just ._ | [ eq ] | refl = fromCompSeq comp'
fromCompSeq (_>>=_ {mx = mx} comp comp') | nothing | [ eq ] with trans (sym eq) (fromCompSeq comp)
fromCompSeq (_>>=_ {mx = mx} comp comp') | nothing | [ eq ] | ()
fromCompSeq (embed eq                  ) = eq
fromCompSeq (assert refl then comp     ) = fromCompSeq comp

record Iso (A B : Set) : Set₁ where
  field
    to   : A → Par B
    from : B → Par A
    to-from-inverse : {x : A} {y : B} → to x ↦ y → from y ↦ x
    from-to-inverse : {y : B} {x : A} → from y ↦ x → to x ↦ y

infix 0 _≅_

_≅_ : Set → Set → Set₁
_≅_ = Iso

id-iso : {A : Set} → A ≅ A
id-iso = record
  { to   = return
  ; from = return
  ; to-from-inverse = λ { {._} (return refl) → return refl }
  ; from-to-inverse = λ { {._} (return refl) → return refl } }

sym-iso : {A B : Set} → A ≅ B → B ≅ A
sym-iso iso = record
  { to   = Iso.from iso
  ; from = Iso.to   iso
  ; to-from-inverse = Iso.from-to-inverse iso
  ; from-to-inverse = Iso.to-from-inverse iso }

trans-iso : {A B C : Set} → A ≅ B → B ≅ C → A ≅ C
trans-iso {A} {B} {C} iso-l iso-r = record
  { to   = Iso.to iso-r <=< Iso.to iso-l
  ; from = Iso.from iso-l <=< Iso.from iso-r
  ; from-to-inverse = λ { (r-comp >>= l-comp) → Iso.from-to-inverse iso-l l-comp >>= Iso.from-to-inverse iso-r r-comp }
  ; to-from-inverse = λ { (l-comp >>= r-comp) → Iso.to-from-inverse iso-r r-comp >>= Iso.to-from-inverse iso-l l-comp } }

prod-unit-iso : {A : Set} → A ≅ A × ⊤
prod-unit-iso = record
  { to   = return ∘ flip _,_ tt
  ; from = return ∘ proj₁
  ; from-to-inverse = λ { {_} {._} (return refl) → return refl }
  ; to-from-inverse = λ { {._}     (return refl) → return refl } }

prod-comm-iso : {A B : Set} → A × B ≅ B × A
prod-comm-iso = record
  { to   = return ∘ swap
  ; from = return ∘ swap
  ; from-to-inverse = λ { {_} {._} (return refl) → return refl }
  ; to-from-inverse = λ { {_} {._} (return refl) → return refl } }
