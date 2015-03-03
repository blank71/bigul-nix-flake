module DynamicallyChecked.SourceFocusing where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Universe
open import DynamicallyChecked.Lens
open import DynamicallyChecked.Conditional

open import Function
open import Data.Unit
open import Data.Bool
import Data.Maybe as Maybe; open Maybe
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin
open import Data.List hiding (filter)
open import Relation.Binary.PropositionalEquality


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

decon : {n : ℕ} {i : Fin n} (F : Functor n) → μ F i ≅ ⟦ F i ⟧ (μ F) × ⊤
decon F = trans-iso (record { to   = λ { (con xs) → just xs }
                            ; from = λ xs → just (con xs)
                            ; to-from-inverse = λ { (con xs) refl → refl }
                            ; from-to-inverse = λ { xs refl → refl } })
                    prod-unit-iso

cond : {A : Set} → (A → Bool) → A ≅ A × ⊤
cond {A} p = trans-iso (record { to   = check 
                               ; from = check
                               ; to-from-inverse = check-inverse
                               ; from-to-inverse = check-inverse })
                       prod-unit-iso
  where
    check : A → Maybe A
    check x = if p x then just x else nothing
    check-inverse : (x : A) {y : A} → (if p x then just x else nothing) ≡ᴶ y → (if p y then just y else nothing) ≡ᴶ x
    check-inverse x eq with p x  | inspect p x
    check-inverse x refl | true  | [ eq ] = if-true eq
    check-inverse x ()   | false | [ eq ]

left-branch : {A B : Set} → A ⊎ B ≅ A × ⊤
left-branch = trans-iso (record { to   = λ { (inj₁ x) → just x; (inj₂ y) → nothing }
                                ; from = λ x → just (inj₁ x)
                                ; to-from-inverse = λ { (inj₁ x) refl → refl ; (inj₂ y) () }
                                ; from-to-inverse = λ { x refl → refl } })
                        prod-unit-iso

right-branch : {A B : Set} → A ⊎ B ≅ B × ⊤
right-branch = trans-iso (record { to   = λ { (inj₁ x) → nothing; (inj₂ y) → just y }
                                 ; from = λ y → just (inj₂ y)
                                 ; to-from-inverse = λ { (inj₁ x) (); (inj₂ y) refl → refl }
                                 ; from-to-inverse = λ { y refl → refl } })
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


--------
-- path language

data Path {n : ℕ} (F : Functor n) : U n → U n → Set₁ where
  child/_   : {i : Fin n} {X : U n}                (p : Path F (F i) X) → Path F (var i)  X
  prod-l/_  : {G H X : U n}                        (p : Path F G     X) → Path F (G ⊗ H)  X
  prod-r/_  : {G H X : U n}                        (p : Path F H     X) → Path F (G ⊗ H)  X
  sum-l/_   : {G H X : U n}                        (p : Path F G     X) → Path F (G ⊕ H)  X
  sum-r/_   : {G H X : U n}                        (p : Path F H     X) → Path F (G ⊕ H)  X
  filter_/_ : {G X : U n} → (⟦ G ⟧ (μ F) → Bool) → (p : Path F G     X) → Path F G        X
  elem_/_   : {G X : U n} → ℕ →                    (p : Path F G     X) → Path F (list G) X

⟦_⟧ᴾ : {n : ℕ} {F : Functor n} {X Y : U n} → Path F X Y → {Z : Set} → ⟦ Y ⟧ (μ F) ⇆ Z → ⟦ X ⟧ (μ F) ⇆ Z
⟦ child/     p ⟧ᴾ lens = focus-lens (decon _)     (⟦ p ⟧ᴾ lens)
⟦ prod-l/    p ⟧ᴾ lens = focus-lens id-iso        (⟦ p ⟧ᴾ lens)
⟦ prod-r/    p ⟧ᴾ lens = focus-lens prod-comm-iso (⟦ p ⟧ᴾ lens)
⟦ sum-l/     p ⟧ᴾ lens = focus-lens left-branch   (⟦ p ⟧ᴾ lens)
⟦ sum-r/     p ⟧ᴾ lens = focus-lens right-branch  (⟦ p ⟧ᴾ lens)
⟦ filter f / p ⟧ᴾ lens = focus-lens (cond f)      (⟦ p ⟧ᴾ lens)
⟦ elem n /   p ⟧ᴾ lens = focus-lens (nth-elem n)  (⟦ p ⟧ᴾ lens)
