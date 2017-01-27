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
open import Data.Empty
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
       (λ _ → inj₂ (inj₁ refl))

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
    (prod replace replace)
    (λ { {(x' , y') , (x , y) , (z , w)} ((x'≡z , y'≡w) , z≡w) → trans x'≡z (trans z≡w (sym y'≡w)) , cong₂ _,_ x'≡z y'≡w })

replace²-equal-view-range : TripleR (uncurry _≡_ ∘ proj₂) replace² (uncurry _≡_)
replace²-equal-view-range =
  conseq
    (λ { {(s , t) , (v , w)} ((s≡v , t≡w) , s≡t) → trans (sym s≡v) (trans s≡t t≡w) })
    (prod replace replace)
    (λ _ → tt , tt)

updateWidth : BiGUL emptyF (kℕ ⊗ kℕ) kℕ
updateWidth = rearrV var (prod {H = one} var (k tt)) (refl , tt) (return refl) (prod replace (skip (const tt)))

updateWidth-correctness : Triple Π updateWidth (λ { ((w' , h') , (_ , h) , v) → w' ≡ v × h' ≡ h })
updateWidth-correctness =
  conseq
    (λ _ → _ , tt , refl)
    (rearrV Π (λ { ((w' , h') , (_ , h) , v) → w' ≡ v × h' ≡ h })
       (conseq
          (λ _ → tt , refl)
          (prod replace skip)
          (λ { {(.v , .h) , (w , h) , (v , _)} ((refl , refl) , _) → _ , (refl , refl) , refl , refl })))
    (λ { {(w' , .h) , (w , h) , v} ((._ , (eq , refl) , refl) , _) → eq , refl })

updateWidth-range : TripleR Π updateWidth Π
updateWidth-range =
  conseq
    (λ _ → tt)
    (rearrV Π
       (conseq
          (λ _ → _ , tt , refl , refl)
          (prod replace skip)
          (λ { tt → tt , tt })))
    id

updateSquare : BiGUL emptyF (kℕ ⊗ kℕ) kℕ
updateSquare =
  case
    (((λ { (w , _) v → ⌊ w Nat.≟ v ⌋ }) ,
      normal (skip proj₁)
             (const true)) ∷
     (((λ _ _ → true) ,
      adaptive (λ { _ v → (v , v) }))) ∷ [])

updateSquare-correctness : Triple Π updateSquare (λ { ((w' , h') , (w , h) , v) → w' ≡ v × (w ≡ v → h' ≡ h) × (w ≢ v → w' ≡ h') })
updateSquare-correctness =
  case
    (((conseq
         (λ { {(w , h) , v} (_ , e , _) → trueToWitness e })
         skip
         (λ { {.(w , h) , (w , h) , v} (refl , _ , e , _) →
              (trueToWitness e , (λ _ → refl) , (λ w≢v → ⊥-elim (w≢v (trueToWitness e)))) , (e , tt) , refl })) ,
      (λ _ → tt)) ∷ᴺ
     ((λ { {(w , h) , v} (tt , _ , ne , _) → tt , inj₁ (trueFromWitness refl) }) ,
      (λ { {(w' , h') , (w , h) , v} ((_ , _ , ne , _) , (w'≡v , v≡v→h'≡v , _)) →
           w'≡v , (λ w≡v → ⊥-elim (falseToWitness ne w≡v)) , (λ _ → trans w'≡v (sym (v≡v→h'≡v refl))) })) ∷ᴬ [])
    (λ _ → inj₂ (inj₁ refl))

updateSquare-range : TripleR Π updateSquare Π
updateSquare-range =
  conseq
    proj₁
    (case
       ((conseq
           (λ { {(w , h) , v} (w≡v , _) → tt , trueFromWitness w≡v , tt })
           skip
           (λ _ → tt) ,
         (λ _ → refl) ,
         (λ _ → tt)) ∷ᴺ •∷ᴬ []))
    inj₁
