-- Small examples for caseS and caseV in Sections 3.4.2 and 3.5.

module BiGUL.CaseExamples where

open import BiGUL.BiGUL
open import BiGUL.Lens
open import BiGUL.Partiality
open import BiGUL.Universe
open import BiGUL.Utilities

open import Function
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin
open import Data.List
open import Relation.Binary.PropositionalEquality


kℕ : {n : ℕ} → U n
kℕ = k ℕ Data.Nat._≟_

emptyF : Functor 0
emptyF ()

isEven : ℕ → Bool
isEven zero          = true
isEven (suc zero)    = false
isEven (suc (suc n)) = isEven n

toEven : BiGUL emptyF kℕ one
toEven = caseS ((return ∘ isEven     , normal   skip) ∷
                ((λ _ → return true) , adaptive (λ n → return (Data.Nat.pred n))) ∷ [])

toEven-completeExpr : BiGULCompleteExpr emptyF toEven
toEven-completeExpr = tt , tt

test-get-toEven : ℕ → Maybe ⊤
test-get-toEven n = runPar (Lens.get (interp emptyF toEven toEven-completeExpr) n)

test-put-toEven : ℕ → Maybe ℕ
test-put-toEven n = runPar (Lens.put (interp emptyF toEven toEven-completeExpr) n tt)

toOdd : BiGUL emptyF kℕ one
toOdd = caseS ((return ∘ not ∘ isEven , normal   skip) ∷
               ((λ _ → return true)   , adaptive (λ n → return (suc n))) ∷ [])

toEvenOrOdd : BiGUL emptyF kℕ (one ⊕ one)
toEvenOrOdd = caseV ((return ∘ is-just ∘ isInj₁ , rearr (left  (k tt)) (k tt) tt toEven) ∷
                     ((λ _ → return true)       , rearr (right (k tt)) (k tt) tt toOdd ) ∷ [])

toEvenOrOdd-completeExpr : BiGULCompleteExpr emptyF toEvenOrOdd
toEvenOrOdd-completeExpr = (return refl , tt , tt) , (return refl , tt , tt) , tt

test-get-toEvenOrOdd : ℕ → Maybe (⊤ ⊎ ⊤)
test-get-toEvenOrOdd n = runPar (Lens.get (interp emptyF toEvenOrOdd toEvenOrOdd-completeExpr) n)

test-put-toEvenOrOdd : ℕ → ⊤ ⊎ ⊤ → Maybe ℕ
test-put-toEvenOrOdd n b = runPar (Lens.put (interp emptyF toEvenOrOdd toEvenOrOdd-completeExpr) n b)
