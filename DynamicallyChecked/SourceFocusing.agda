module DynamicallyChecked.SourceFocusing where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Universe
open import DynamicallyChecked.Lens

open import Function
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin
open import Data.List hiding (filter)
open import Relation.Binary.PropositionalEquality


focus-lens : {S F S' V : Set} → S ≅ F × S' → F ⇆ V → S ⇆ V
focus-lens {S} {F} {S'} {V} iso lens = record
  { put = λ s v → Iso.to iso s >>= λ { (focus , residual) →
                  Lens.put lens focus v >>= λ focus' →
                  Iso.from iso (focus' , residual) }
  ; get = (Lens.get lens ∘ proj₁) <=< Iso.to iso 
  ; PutGet = λ { (to-s↦focus,residual >>= put-focus-v↦focus' >>= from-focus',residual↦s') →
                 Iso.from-to-inverse iso from-focus',residual↦s' >>= Lens.PutGet lens put-focus-v↦focus' }
  ; GetPut = λ { (to-s↦focus,residual >>= get-focus↦v) →
                 to-s↦focus,residual >>= Lens.GetPut lens get-focus↦v >>= Iso.to-from-inverse iso to-s↦focus,residual } }

-- path components

decon : {n : ℕ} {i : Fin n} (F : Functor n) → μ F i ≅ ⟦ F i ⟧ (μ F) × ⊤
decon F = trans-iso (record { to   = λ { (con xs) → return xs }
                            ; from = λ xs → return (con xs)
                            ; to-from-inverse = λ { {con xs} (return refl) → return refl }
                            ; from-to-inverse = λ { {_} {._} (return refl) → return refl } })
                    prod-unit-iso

cond : {A : Set} → (A → Bool) → A ≅ A × ⊤
cond {A} p = trans-iso (record { to = check; from = check; to-from-inverse = check-inverse; from-to-inverse = check-inverse })
                       prod-unit-iso
  where
    check : A → Par A
    check x = assert (p x) then return x
    check-inverse : {x y : A} → check x ↦ y → check y ↦ x
    check-inverse (assert p-x≡true then return refl) = assert p-x≡true then return refl

left-branch : {A B : Set} → A ⊎ B ≅ A × ⊤
left-branch {A} {B} =
  trans-iso (record { to   = to
                    ; from = λ x → return (inj₁ x)
                    ; to-from-inverse = λ { {inj₁ x} (return refl) → return refl ; {inj₂ y} () }
                    ; from-to-inverse = λ { {_} {._} (return refl) → return refl } })
            prod-unit-iso
  where
    to : A ⊎ B → Par A
    to (inj₁ x) = return x
    to (inj₂ y) = fail

right-branch : {A B : Set} → A ⊎ B ≅ B × ⊤
right-branch {A} {B} =
  trans-iso (record { to   = to
                    ; from = λ y → return (inj₂ y)
                    ; to-from-inverse = λ { {inj₁ x} (); {inj₂ y} (return refl) → return refl }
                    ; from-to-inverse = λ { {_} {._} (return refl) → return refl } })
            prod-unit-iso
  where
    to : A ⊎ B → Par B
    to (inj₁ x) = fail
    to (inj₂ y) = return y

nth-elem : {A : Set} → ℕ → List A ≅ A × (List A × List A)
nth-elem {A} n = record
  { to   = split n
  ; from = λ { (x , ys , zs) → unsplit n x ys zs }
  ; from-to-inverse = λ { {x , ys , zs} → unsplit-split-inverse n x ys zs }
  ; to-from-inverse = split-unsplit-inverse n }
  where
    split : ℕ → List A → Par (A × (List A × List A))
    split n       []       = fail
    split zero    (x ∷ xs) = return (x , [] , xs)
    split (suc n) (x ∷ xs) = liftPar (λ { (y , zs , ws) → y , x ∷ zs , ws }) (split n xs)
    unsplit : ℕ → A → List A → List A → Par (List A)
    unsplit zero    x []       zs = return (x ∷ zs)
    unsplit (suc n) x []       zs = fail
    unsplit zero    x (y ∷ ys) zs = fail
    unsplit (suc n) x (y ∷ ys) zs = liftPar (_∷_ y) (unsplit n x ys zs)
    unsplit-split-inverse : (n : ℕ) (x : A) (ys zs : List A) {ws : List A} →
                            unsplit n x ys zs ↦ ws → split n ws ↦ (x , ys , zs)
    unsplit-split-inverse zero    x []       zs (return refl) = return refl
    unsplit-split-inverse (suc n) x []       zs ()
    unsplit-split-inverse zero    x (y ∷ ys) zs ()
    unsplit-split-inverse (suc n) x (y ∷ ys) zs (unsplit↦ >>= return refl) =
      unsplit-split-inverse n x ys zs unsplit↦ >>= return refl
    split-unsplit-inverse : (n : ℕ) {ws : List A} {x : A} {ys zs : List A} →
                            split n ws ↦ (x , ys , zs) → unsplit n x ys zs ↦ ws
    split-unsplit-inverse n       {[]    } ()
    split-unsplit-inverse zero    {w ∷ ws} (return refl) = return refl
    split-unsplit-inverse (suc n) {w ∷ ws} (split↦ >>= return refl) = split-unsplit-inverse n split↦ >>= return refl


--------
-- path language

data Path {n : ℕ} (F : Functor n) : U n → U n → Set₁ where
  child⟩_   : {i : Fin n} {X : U n}                (p : Path F (F i) X) → Path F (var i)  X
  prod-l⟩_  : {G H X : U n}                        (p : Path F G     X) → Path F (G ⊗ H)  X
  prod-r⟩_  : {G H X : U n}                        (p : Path F H     X) → Path F (G ⊗ H)  X
  sum-l⟩_   : {G H X : U n}                        (p : Path F G     X) → Path F (G ⊕ H)  X
  sum-r⟩_   : {G H X : U n}                        (p : Path F H     X) → Path F (G ⊕ H)  X
  filter_⟩_ : {G X : U n} → (⟦ G ⟧ (μ F) → Bool) → (p : Path F G     X) → Path F G        X
  elem_⟩_   : {G X : U n} → ℕ →                    (p : Path F G     X) → Path F (list G) X

⟦_⟧ᴾ : {n : ℕ} {F : Functor n} {X Y : U n} → Path F X Y → {Z : Set} → ⟦ Y ⟧ (μ F) ⇆ Z → ⟦ X ⟧ (μ F) ⇆ Z
⟦ child⟩     p ⟧ᴾ lens = focus-lens (decon _)     (⟦ p ⟧ᴾ lens)
⟦ prod-l⟩    p ⟧ᴾ lens = focus-lens id-iso        (⟦ p ⟧ᴾ lens)
⟦ prod-r⟩    p ⟧ᴾ lens = focus-lens prod-comm-iso (⟦ p ⟧ᴾ lens)
⟦ sum-l⟩     p ⟧ᴾ lens = focus-lens left-branch   (⟦ p ⟧ᴾ lens)
⟦ sum-r⟩     p ⟧ᴾ lens = focus-lens right-branch  (⟦ p ⟧ᴾ lens)
⟦ filter f ⟩ p ⟧ᴾ lens = focus-lens (cond f)      (⟦ p ⟧ᴾ lens)
⟦ elem n ⟩   p ⟧ᴾ lens = focus-lens (nth-elem n)  (⟦ p ⟧ᴾ lens)
