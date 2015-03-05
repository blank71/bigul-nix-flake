module DynamicallyChecked.Universe where

open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin
open import Data.List


data U (n : ℕ) : Set₁ where
  var  : (i : Fin n) → U n
  k    : (A : Set)   → U n
  _⊕_  : (F G : U n) → U n
  _⊗_  : (F G : U n) → U n
  list : (F : U n)   → U n

⟦_⟧ : {n : ℕ} → U n → (Fin n → Set) → Set
⟦ var  i ⟧ Xs = Xs i
⟦ k A    ⟧ Xs = A
⟦ F ⊕ G  ⟧ Xs = ⟦ F ⟧ Xs ⊎ ⟦ G ⟧ Xs
⟦ F ⊗ G  ⟧ Xs = ⟦ F ⟧ Xs × ⟦ G ⟧ Xs
⟦ list F ⟧ Xs = List (⟦ F ⟧ Xs)

Functor : ℕ → Set₁
Functor n = Fin n → U n

data μ {n : ℕ} (F : Functor n) : Fin n → Set where
  con : {i : Fin n} → ⟦ F i ⟧ (μ F) → μ F i
