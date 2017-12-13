module HoareLogic.Continuity where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Function
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Relation.Binary.PropositionalEquality


_≼_ : {S V : Set} → S ⇆ V → S ⇆ V → Set₁
_≼_ {S} {V} l r = {s' s : S} {v : V} → Lens.put l s v ↦ s' → Lens.put r s v ↦ s'

info-order-get : {S V : Set} (l r : S ⇆ V) → l ≼ r → {s : S} {v : V} → Lens.get l s ↦ v → Lens.get r s ↦ v
info-order-get l r l≼r get-l-s↦v = Lens.PutGet r (l≼r (Lens.GetPut l get-l-s↦v))

IsChain : {S V : Set} → (ℕ → S ⇆ V) → Set₁
IsChain c = (i : ℕ) → c i ≼ c (suc i)

LeastUpperBound : {S V : Set} → (ℕ → S ⇆ V) → S ⇆ V → Set₁
LeastUpperBound {S} {V} c l =
  ({s : S} {v : V} {s' : S} → Lens.put l s v ↦ s' → Σ[ i ∈ ℕ ] Lens.put (c i) s v ↦ s') ×
  ({s : S} {v : V} → FailedCompSeq (Lens.put l s v) → (i : ℕ) → FailedCompSeq (Lens.put (c i) s v))

◂-continuous : {A B C : Set} (c : ℕ → A ⇆ B) (l : A ⇆ B) → LeastUpperBound c l →
               (iso : B ≅ C) (r : A ⇆ C) → LeastUpperBound (λ i → c i ◂ iso) r → (l ◂ iso) ≼ r
◂-continuous c l lub-c-l iso r lub-c◂iso-r (from-iso↦ >>= put-l↦) = let (i , put-c-i↦) = proj₁ lub-c-l put-l↦ in {!!}
