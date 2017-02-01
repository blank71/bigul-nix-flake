open import DynamicallyChecked.Universe
open import Data.Nat as Nat

module HoareLogic.Examples.ReplaceAll (Aᵁ : {n : ℕ} → U n) where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Rearrangement
open import DynamicallyChecked.BiGUL
open import HoareLogic.Utilities
open import HoareLogic.Semantics
open import HoareLogic.Rearrangement
open import HoareLogic.Triple

open import Function
open import Data.Empty using (⊥-elim)
open import Data.Product as Product
open import Data.Sum
open import Data.Bool
open import Data.Nat.Properties
open import Data.List as List
open import Data.List.Any as Any
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


F : Functor 1
F zero = one ⊕ (Aᵁ ⊗ var zero)
F (suc ())

A : Set
A = ⟦ Aᵁ ⟧ (μ F)

ListA : Set
ListA = μ F zero

pattern []ᴹ       = con (inj₁ tt)
pattern _∷ᴹ_ x xs = con (inj₂ (x , xs))

infixr 5 _∷ᴹ_

toList : ListA → List A
toList []ᴹ       = []
toList (x ∷ᴹ xs) = x ∷ toList xs

replaceAllᴮ : BiGUL F (var zero) Aᵁ → BiGUL F (var zero) Aᵁ
replaceAllᴮ rec =
  case
    (((λ { []ᴹ _ → true
         ; _   _ → false }) ,
      adaptive (λ _ x → x ∷ᴹ []ᴹ)) ∷
     ((λ { (_ ∷ᴹ []ᴹ) _ → true
         ; _          _ → false }) ,
      normal
        (rearrS (con (right (prod var (con (left (k tt)))))) var (inj₁ refl) (return refl >>= return refl)
           replace)
        (λ { (_ ∷ᴹ []ᴹ) → true
           ; _          → false })) ∷
     ((λ _ _ → true) ,
      normal
        (rearrS (con (right (prod var var))) (prod var var) (inj₁ refl , inj₂ refl) (return refl >>= return refl)
           (rearrV var (prod var var) (refl , refl) (return refl)
              (prod replace rec)))
        (λ { (_ ∷ᴹ _ ∷ᴹ _) → true
           ; _             → false })) ∷ [])

Post : ℙ (ListA × ListA × A)
Post (ss' , ss , v) = ((s' : A) → Any (_≡ s') (toList ss') → s' ≡ v) ×
                      (case ss of λ { []ᴹ → ⊤; (_ ∷ᴹ _) → length (toList ss') ≡ length (toList ss) })

replaceAll-correctness :
  (n : ℕ) (rec : BiGUL F (var zero) Aᵁ) →
  ({m : ℕ} → Triple (((_≡ m) ∘ length ∘ toList ∘ proj₁) ∩ (λ _ → m < n)) rec Post) →
  Triple ((_≡ n) ∘ length ∘ toList ∘ proj₁) (replaceAllᴮ rec) Post
replaceAll-correctness n rec rec-t =
  conseq {R = λ { (ss , v) → length (toList ss) ≡ n ⊎ (n ≡ 0 × length (toList ss) ≡ 1) }}
    inj₁
    (case
       (((λ { {[]ᴹ    , _} (inj₁ 0≡n , _) → (inj₂ (sym 0≡n , refl)) , refl , inj₁ refl
            ; {[]ᴹ    , _} (inj₂ (_ , ()) , _)
            ; {_ ∷ᴹ _ , _} (_ , () , _) }) ,
         (λ { {ss' , []ᴹ    , _} ((inj₁ 0≡n , _) , post , _) → post , tt
            ; {_ , []ᴹ    , _} ((inj₂ (_ , ()) , _) , _)
            ; {_ , _ ∷ᴹ _ , _} ((_ , () , _) , _) })) ∷ᴬ
        (conseq
           (λ { {[]ᴹ         , _} (_ , () , _)
              ; {_ ∷ᴹ []ᴹ    , _} _ → _ , (refl , refl) , tt
              ; {_ ∷ᴹ _ ∷ᴹ _ , _} (_ , () , _) })
           (rearrS (λ _ → ⊤) (λ { ((s' , _) , _ , v) → s' ≡ v })
              (conseq
                 (λ _ → tt)
                 replace
                 (λ { {s' , s , v} (s'≡v , _) → _ , s'≡v , refl , refl })))
           (λ { {_ , []ᴹ , _} (_ , _ , () , _)
              ; {[]ᴹ , s ∷ᴹ []ᴹ , v} ((_ , _ , () , _) , _)
              ; {s' ∷ᴹ []ᴹ , s ∷ᴹ []ᴹ , v} ((((s'* , _) , (s* , _)) , s'*≡v , (s'≡s'* , _) , s≡s* , _) , _) →
                  ((λ { .s' (here refl) → trans s'≡s'* s'*≡v; x (there ()) }) , refl) , (refl , refl , tt) , refl
              ; {_ ∷ᴹ _ ∷ᴹ _ , s ∷ᴹ []ᴹ , v} ((_ , _ , (_ , ()) , _) , _)
              ; {_ , _ ∷ᴹ _ ∷ᴹ _ , _} (_ , _ , () , _) }) ,
         (λ _ → tt , tt)) ∷ᴺ
        (conseq
           (λ { {[]ᴹ , _} (_ , _ , _ , () , _)
              ; {_ ∷ᴹ []ᴹ , _} (_ , _ , () , _)
              ; {_ ∷ᴹ _ ∷ᴹ ss , _} (inj₁ eq , _) → _ , (refl , refl) , eq
              ; {_ ∷ᴹ _ ∷ᴹ ss , _} (inj₂ (_ , ()) , _) })
           (rearrS (λ { ((_ , _ ∷ᴹ ss) , v) → 2 + length (toList ss) ≡ n; _ → ⊥ })
                   (λ { ((x , y ∷ᴹ ss') , (_ , _ ∷ᴹ ss) , v) →
                        x ≡ v × y ≡ v ×
                        ((s' : A) → Any (_≡ s') (toList ss') → s' ≡ v) ×
                        length (toList ss') ≡ length (toList ss)
                      ; _ → ⊥ })
              (conseq
                 (λ { {(_ , []ᴹ) , _} → λ { (_ , (refl , refl) , ()) } 
                    ; {(_ , _ ∷ᴹ _) , _} → λ { (_ , (refl , refl) , eq) → _ , eq , refl } })
                 (rearrV (λ { ((_ , _ ∷ᴹ ss) , v) → suc (suc (length (toList ss))) ≡ n; _ → ⊥ })
                         (λ { ((x' , y' ∷ᴹ ss') , (_ , _ ∷ᴹ ss) , v) →
                              x' ≡ v × y' ≡ v ×
                              ((s' : A) → Any (_≡ s') (toList ss') → s' ≡ v) ×
                              length (toList ss') ≡ length (toList ss)
                            ; _ → ⊥ })
                    (conseq
                       (λ { {(_ , []ᴹ) , _} (_ , () , _)
                          ; {(_ , _ ∷ᴹ _) , (v , w)} (_ , leneq , refl , v≡w) → tt , cong pred leneq , pred-lemma leneq })
                       (prod replace (rec-t {pred n}))
                       (λ { {_ , (_ , []ᴹ) , _} (_ , _ , () , _)
                          ; {(_ , []ᴹ) , (_ , _ ∷ᴹ _) , _} ((_ , _ , ()) , _)
                          ; {(x' , y' ∷ᴹ ss') , (x , y ∷ᴹ ss) , (v , w)} ((x'≡v , post , leneq) , _ , _ , refl , v≡w) →
                              v , (x'≡v , trans (post y' (here refl)) (sym v≡w) ,
                                   (λ s' i → trans (post s' (there i)) (sym v≡w)) , cong pred leneq) , (refl , v≡w) })))
                 (λ { {(_ , []ᴹ) , (_ , []ᴹ) , _} ((_ , () , _) , _)
                    ; {(_ , _ ∷ᴹ _) , (_ , []ᴹ) , _} ((_ , () , _) , _)
                    ; {(_ , []ᴹ) , (_ , _ ∷ᴹ _) , _} ((_ , () , _) , _)
                    ; {(x' , y' ∷ᴹ ss') , (x , y ∷ᴹ ss) , v} ((_ , post , refl) , _ , (refl , refl) , q) →
                        _ , post , (refl , refl) , (refl , refl) })))
           (λ { {_ , []ᴹ , _} (_ , _ , _ , _ , () , _)
              ; {_ , _ ∷ᴹ []ᴹ , _} (_ , _ , _ , () , _)
              ; {[]ᴹ , _ ∷ᴹ _ ∷ᴹ _ , _} ((_ , _ , () , _) , _)
              ; {_ ∷ᴹ []ᴹ , _ ∷ᴹ _ ∷ᴹ _ , _} ((((_ , .[]ᴹ) , _) , () , (_ , refl) , _) , _)
              ; {x' ∷ᴹ y' ∷ᴹ ss' , x ∷ᴹ y ∷ᴹ ss , v}
                ((((.x' , .(y' ∷ᴹ ss')) , (.x , .(y ∷ᴹ ss))) ,
                  (x'≡v , y'≡v , post , length-ss'≡length-ss) , (refl , refl) , (refl , refl)) , _) →
                ((λ { .x' (here refl) → x'≡v
                    ; .y' (there (here refl)) → y'≡v
                    ; s' (there (there i)) → post s' i }) ,
                 cong suc (cong suc length-ss'≡length-ss)) , (refl , refl , refl , tt) , refl }) ,
         (λ { {[]ᴹ        } ()
            ; {_ ∷ᴹ []ᴹ   } ()
            ; {_ ∷ᴹ _ ∷ᴹ _} _ → refl , tt , tt })) ∷ᴺ [])
       (λ _ → inj₂ (inj₂ (inj₁ refl))))
    proj₁
