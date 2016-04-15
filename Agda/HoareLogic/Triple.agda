module HoareLogic.Triple where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality

open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality


Pred : Set → Set₁
Pred A = A → Set

_~_ : Set → Set → Set₁
A ~ B = A → B → Set

_⊆_ : {A B : Set} → (A ~ B) → (A ~ B) → Set
R ⊆ S = ∀ {a b} → R a b → S a b

_∩_ : {A B : Set} → (A ~ B) → (A ~ B) → (A ~ B)
(R ∩ S) a b = R a b × S a b

boolPred : {A B : Set} → (A → B → Bool) → A ~ B
boolPred p a b = p a b ≡ true

-- "directional" union
boolBiasedUnion : {A : Set} → List (A → Bool) → Pred A
boolBiasedUnion []       a = ⊥
boolBiasedUnion (p ∷ ps) a = p a ≡ true ⊎ (p a ≡ false × boolBiasedUnion ps a)

Sound : {S V : Set} → (S ~ V) → (S → V → Par S) → (S ~ V) → Set₁
Sound {S} {V} R f R' = (s : S) (v : V) → R s v → Σ[ s' ∈ S ] ((f s v ↦ s') × R' s' v)
