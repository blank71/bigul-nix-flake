module HoareLogic.Triple where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Function
open import Data.Product as Product
open import Data.Sum
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality


ℙ : Set → Set₁
ℙ A = A → Set

_⊆_ : {A : Set} → ℙ A → ℙ A → Set
S ⊆ T = ∀ {a} → S a → T a

infix 2 _⊆_

∅ : {A : Set} → ℙ A
∅ _ = ⊥

Π : {A : Set} → ℙ A
Π _ = ⊤

True : ℙ Bool
True b = b ≡ true

False : ℙ Bool
False b = b ≡ false

_∪_ : {A : Set} → ℙ A → ℙ A → ℙ A
(S ∪ T) a = S a ⊎ T a

infixr 3 _∪_

_∩_ : {A : Set} → ℙ A → ℙ A → ℙ A
(S ∩ T) a = S a × T a

infixr 3 _∩_

_⇒_ : {A B : Set} → ℙ (A × B) → ℙ (A × B) → ℙ (A × B)
(R ⇒ S) (a , b) = R (a , b) → S (a , b)

_⋈_ : {A B C : Set} → ℙ (A × B) → ℙ (A × C) → ℙ (A × B × C)
(R ⋈ S) (a , b , c) = R (a , b) × S (a , c)

∑ : {A B : Set} → ℙ (A × B) → ℙ B
∑ R b = ∃ λ a → R (a , b) 

_•_ : {A B C : Set} → ℙ (A × B) → ℙ (B × C) → ℙ (A × C)
R • S = ∑ ((R ∘ swap) ⋈ S)

-- find a largest predicate on B for filtering R such that the result is included in S
_\\_ : {A B : Set} → ℙ (A × B) → ℙ (A × B) → ℙ B
(R \\ S) b = ∀ a → R (a , b) → S (a , b)

Sound : {S V : Set} → ℙ (S × V) → (S → V → Par S) → ℙ (S × S × V) → Set₁
Sound {S} {V} R f R' = (sv : S × V) → let (s , v) = sv in R (s , v) → Σ[ s' ∈ S ] ((f s v ↦ s') × R' (s' , s , v))

consequence : {S V : Set} (R : ℙ (S × V)) (f : S → V → Par S) (R' : ℙ (S × S × V)) → Sound R f R' →
              (Q : ℙ (S × V)) → Q ⊆ R → (Q' : ℙ (S × S × V)) → R' ∩ (R ∘ proj₂) ⊆ Q' → Sound Q f Q'
consequence R f R' sound Q Q⊆R Q' R'∩R∘proj₂⊆Q' (s , v) Q-s-v =
  let (s' , f-s-v↦s' , R'-s'-s-v) = sound (s , v) (Q⊆R Q-s-v) in s' , f-s-v↦s' , R'∩R∘proj₂⊆Q' (R'-s'-s-v , Q⊆R Q-s-v)

get-correctness : {S V : Set} (R : ℙ (S × V)) (l : S ⇆ V) (R' : ℙ (S × V)) →
                  Sound R (Lens.put l) (R' ∘ Product.map id proj₂) →
                  {s : S} {v : V} → Lens.get l s ↦ v → (R ⇒ R') (s , v)
get-correctness R l R' sound get↦ Rsv with sound _ Rsv
get-correctness R l R' sound get↦ Rsv | (s' , put↦ , R's'v) with CompSeq-deterministic put↦ (Lens.GetPut l get↦)
get-correctness R l R' sound get↦ Rsv | (s' , put↦ , R's'v) | refl = R's'v

hippocratic-triple : {S V : Set} (R : ℙ (S × V)) (l : S ⇆ V) →
                     Sound R (Lens.put l) (uncurry _≡_ ∘ Product.map id proj₁) →
                     (s : S) (v : V) → R (s , v) → Lens.get l s ↦ v
hippocratic-triple R l sound s v Rsv with sound (s , v) Rsv
hippocratic-triple R l sound s v Rsv | .s , put↦ , refl = Lens.PutGet l put↦
