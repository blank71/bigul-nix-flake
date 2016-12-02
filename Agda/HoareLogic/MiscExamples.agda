module HoareLogic.MiscExamples where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Universe
open import DynamicallyChecked.BiGUL
open import HoareLogic.Semantics
open import HoareLogic.Triple
open import HoareLogic.Utilities

open import Function
open import Data.Product
open import Data.Sum as Sum
open import Data.Bool
open import Data.Nat
open import Data.List
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality


emb : {n : ℕ} {F : Functor n} {S V : U n} →
      (⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F)) → (⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)) →
      BiGUL F S V
emb {V = V} g p = case (((λ s v → ⌊ U-dec V (g s) v ⌋) ,
                           normal (skip g)
                                  (λ _ → true)) ∷
                        ((λ _ _ → true) ,
                           adaptive p) ∷ [])

emb-correctness : {n : ℕ} {F : Functor n} {S V : U n}
                  (g : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F)) (p : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)) →
                  ({s : ⟦ S ⟧ (μ F)} {v : ⟦ V ⟧ (μ F)} → g (p s v) ≡ v) →
                  Triple Π (emb {F = F} {S} {V} g p) (λ { (s' , _ , v) → g s' ≡ v })
emb-correctness g p PutGet =
  case ((conseq (λ { (_ , cond , _) → trueToWitness cond }) skip
                (λ { {.s , s , v} (refl , eq) → eq , (trueFromWitness eq , tt) , refl }) , (λ _ → tt)) ∷ᴺ
        ((λ _ → tt , inj₁ (trueFromWitness PutGet)) , (λ { (_ , eq) → eq })) ∷ᴬ [])
       (λ _ → Sum.map id < id , const (inj₁ refl) > boolExcludedMiddle)
