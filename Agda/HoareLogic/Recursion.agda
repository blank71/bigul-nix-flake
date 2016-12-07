module HoareLogic.Recursion where

open import DynamicallyChecked.Universe
open import DynamicallyChecked.BiGUL
open import HoareLogic.Semantics
open import HoareLogic.Triple

open import Function
open import Data.Product
open import Data.Nat as Nat
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


expand : ℕ → {n : ℕ} {F : Functor n} {S V : U n} → (BiGUL F S V → BiGUL F S V) → BiGUL F S V
expand zero    f = fail
expand (suc n) f = f (expand n f)

expandTriple :
  {n : ℕ} {F : Functor n} {S V : U n} (f : BiGUL F S V → BiGUL F S V)
  (measure : ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F) → ℕ) →
  (R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))) (R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))) →
  ((n : ℕ) (rec : BiGUL F S V) → ((m : ℕ) → m < n → Triple (R ∩ ((_≡ m) ∘ measure)) rec R') →
                                 Triple (R ∩ ((_≡ n) ∘ measure)) (f rec) R') →
  (n : ℕ) (m : ℕ) → m ≤ n → Triple (R ∩ ((_≡ m) ∘ measure)) (expand (suc n) f) R'
expandTriple f measure R R' g zero    .zero    z≤n      = g zero fail (λ _ ())
expandTriple f measure R R' g (suc n) .zero    z≤n      = g zero (f (expand n f)) (λ _ ())
expandTriple f measure R R' g (suc n) (suc m) (s≤s m≤n) =
  g (suc m) (f (expand n f))
    (λ { m' (s≤s m'≤m) → expandTriple f measure R R' g n m' (DecTotalOrder.trans Nat.decTotalOrder m'≤m m≤n) })
