module MutuallyRecursiveUniverse where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin
open import Data.List


data U (n : ℕ) : Set₁ where
  var  : (i : Fin n) → U n
  zero : U n
  one  : U n
  k    : (A : Set) → U n
  _⊕_  : (F G : U n) → U n
  _⊗_  : (F G : U n) → U n
  list : (F : U n) → U n

⟦_⟧ : {n : ℕ} → U n → (Fin n → Set) → Set
⟦ var  i ⟧ Xs = Xs i
⟦ zero   ⟧ Xs = ⊥
⟦ one    ⟧ Xs = ⊤
⟦ k A    ⟧ Xs = A
⟦ F ⊕ G  ⟧ Xs = ⟦ F ⟧ Xs ⊎ ⟦ G ⟧ Xs
⟦ F ⊗ G  ⟧ Xs = ⟦ F ⟧ Xs × ⟦ G ⟧ Xs
⟦ list F ⟧ Xs = List (⟦ F ⟧ Xs)

Functor : ℕ → Set₁
Functor n = Fin n → U n

data μ {n : ℕ} (F : Functor n) : Fin n → Set where
  con : {i : Fin n} → ⟦ F i ⟧ (μ F) → μ F i

-- equal-or-not : {n : ℕ} (i j : Fin n) → Dec (i ≡ j)
-- equal-or-not zero    zero    = yes refl
-- equal-or-not zero    (suc _) = no (λ ())
-- equal-or-not (suc _) zero    = no (λ ())
-- equal-or-not (suc i) (suc j) with equal-or-not i j
-- equal-or-not (suc i) (suc j) | yes eq = yes (cong suc eq)
-- equal-or-not (suc i) (suc j) | no neq = no (neq ∘ cong-pred)
--   where
--     cong-pred : {n : ℕ} {i j : Fin n} → (Fin (suc n) ∋ suc i) ≡ suc j → i ≡ j
--     cong-pred refl = refl
