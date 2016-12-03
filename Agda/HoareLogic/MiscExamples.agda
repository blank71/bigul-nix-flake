module HoareLogic.MiscExamples where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Universe
open import DynamicallyChecked.Rearrangement
open import DynamicallyChecked.BiGUL
open import HoareLogic.Semantics
open import HoareLogic.Triple
open import HoareLogic.Utilities

open import Function
open import Data.Product as Product
open import Data.Sum as Sum
open import Data.Bool
open import Data.Nat as Nat
open import Data.Fin
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
                (λ { {.s , s , v} (refl , _ , equa , _) → trueToWitness equa , (equa , tt) , refl }) , (λ _ → tt)) ∷ᴺ
        ((λ _ → tt , inj₁ (trueFromWitness PutGet)) , (λ { (_ , eq) → eq })) ∷ᴬ [])
       (λ _ → Sum.map id < id , const (inj₁ refl) > boolExcludedMiddle)

emptyF : Functor 0
emptyF ()

kℕ : U 0
kℕ = k ℕ Nat._≟_

replace² : BiGUL emptyF (kℕ ⊗ kℕ) (kℕ ⊗ kℕ)
replace² = prod replace replace

replace²-equal-view-correctness : Triple (uncurry _≡_ ∘ proj₂) replace² (uncurry _≡_ ∘ proj₁ ∩ uncurry _≡_ ∘ Product.map id proj₂)
replace²-equal-view-correctness =
  conseq
    (λ _ → tt , tt)
    (prod _ _ replace _ _ replace)
    (λ { {(x' , y') , (x , y) , (z , w)} ((x'≡z , y'≡w) , z≡w) → trans x'≡z (trans z≡w (sym y'≡w)) , cong₂ _,_ x'≡z y'≡w })

updateSquare : BiGUL emptyF (kℕ ⊗ kℕ) kℕ
updateSquare = rearrV var (prod var var) (refl , refl) (return refl) replace²

updateSquare-correctness : Triple Π updateSquare (λ { ((w' , h') , _ , v) → w' ≡ v × h' ≡ v })
updateSquare-correctness =
  conseq
    (λ _ → _ , tt , refl)
    (rearrV Π (λ { ((w' , h') , _ , v) → w' ≡ v × h' ≡ v })
       (conseq
          (λ { {(w , h) , (vl , vr)} (x , _ , eqa , eqb) → trans (sym eqa) eqb })
          replace²-equal-view-correctness
          (λ { {(w' , h') , (w , h) , (vl , vr)} ((w'≡h' , w',h'≡vl,vr) , x , _ , x≡vl , x≡vr) →
               h' , (w'≡h' , refl) , trans (cong proj₂ w',h'≡vl,vr) (trans (sym x≡vr) x≡vl) , cong proj₂ w',h'≡vl,vr })))
    (λ { {(w' , h') , (w , h) , v} ((x , (w'≡x , h'≡x) , v≡x) , _) → trans w'≡x (sym v≡x) , trans h'≡x (sym v≡x) })

updateWidth : BiGUL emptyF (kℕ ⊗ kℕ) kℕ
updateWidth = rearrV var (prod {H = one} var (k tt)) (refl , tt) (return refl) (prod replace (skip (const tt)))

updateWidth-correctness : Triple Π updateWidth (λ { ((w' , h') , (_ , h) , v) → w' ≡ v × h' ≡ h })
updateWidth-correctness =
  conseq
    (λ _ → _ , tt , refl)
    (rearrV Π (λ { ((w' , h') , (_ , h) , v) → w' ≡ v × h' ≡ h })
       (conseq
          (λ _ → tt , refl)
          (prod _ _ replace _ _ skip)
          (λ { {(.v , .h) , (w , h) , (v , _)} ((refl , refl) , _) → _ , (refl , refl) , refl , refl })))
    (λ { {(w' , .h) , (w , h) , v} ((._ , (eq , refl) , refl) , _) → eq , refl })
