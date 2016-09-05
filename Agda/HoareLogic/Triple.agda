module HoareLogic.Triple where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality

open import Function
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality


ℙ : Set → Set₁
ℙ A = A → Set

_⊆_ : {A : Set} → ℙ A → ℙ A → Set
S ⊆ T = ∀ {a} → S a → T a

_∩_ : {A : Set} → ℙ A → ℙ A → ℙ A
(S ∩ T) a = S a × T a

infixr 2 _∩_

inv : {A B : Set} → (A → B) → ℙ B → ℙ A
inv f p = p ∘ f

boolℙ : {A : Set} → (A → Bool) → ℙ A
boolℙ p a = p a ≡ true

-- "directional" union
boolBiasedUnion : {A : Set} → List (A → Bool) → ℙ A
boolBiasedUnion []       a = ⊥
boolBiasedUnion (p ∷ ps) a = p a ≡ true ⊎ (p a ≡ false × boolBiasedUnion ps a)

Sound : {S V : Set} → ℙ (S × V) → (S → V → Par S) → ℙ (S × S × V) → Set₁
Sound {S} {V} R f R' = (sv : S × V) → let (s , v) = sv in R (s , v) → Σ[ s' ∈ S ] ((f s v ↦ s') × R' (s' , s , v))

propagation-soundness : {S V : Set} (R : ℙ (S × V)) (f : S → V → Par S) (R' : ℙ (S × S × V)) → Sound R f R' → Sound R f (R' ∩ inv proj₂ R)
propagation-soundness R f R' sound sv Rsv = let (s' , f↦ , R's'sv) = sound sv Rsv in s' , f↦ , (R's'sv , Rsv)
