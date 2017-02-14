open import DynamicallyChecked.Universe
open import Data.Nat as Nat

module HoareLogic.Examples.Alignment (Sᵁ Vᵁ : {n : ℕ} → U n) where

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


F : Functor 2
F zero       = one ⊕ (Sᵁ ⊗ var zero)
F (suc zero) = one ⊕ (Vᵁ ⊗ var (suc zero))
F (suc (suc ()))

S : Set
S = ⟦ Sᵁ ⟧ (μ F)

V : Set
V = ⟦ Vᵁ ⟧ (μ F)

ListS : Set
ListS = μ F zero

ListV : Set
ListV = μ F (suc zero)

pattern []ᴹ       = con (inj₁ tt)
pattern _∷ᴹ_ x xs = con (inj₂ (x , xs))

infixr 5 _∷ᴹ_

toList₀ : ListS → List S
toList₀ []ᴹ       = []
toList₀ (s ∷ᴹ ss) = s ∷ toList₀ ss

toList₁ : ListV → List V
toList₁ []ᴹ       = []
toList₁ (v ∷ᴹ vs) = v ∷ toList₁ vs

extract : {K : Set} → Decidable (_≡_ {A = K}) → (S → K) → (V → K) → V → ListS → ListS
extract keq ks kv v []ᴹ       = []ᴹ
extract keq ks kv v (s ∷ᴹ ss) with keq (ks s) (kv v)
extract keq ks kv v (s ∷ᴹ ss) | yes _ = s ∷ᴹ ss
extract keq ks kv v (s ∷ᴹ ss) | no  _ with extract keq ks kv v ss
extract keq ks kv v (s ∷ᴹ ss) | no  _ | []ᴹ         = s ∷ᴹ []ᴹ
extract keq ks kv v (s ∷ᴹ ss) | no  _ | (s' ∷ᴹ ss') = s' ∷ᴹ s ∷ᴹ ss'

headMatch : {K : Set} → Decidable (_≡_ {A = K}) → (S → K) → (V → K) → ListS → ListV → Bool
headMatch keq ks kv (s ∷ᴹ _) (v ∷ᴹ _) = ⌊ keq (ks s) (kv v) ⌋
headMatch keq ks kv _        _        = false

keyAlignᴮ : {K : Set} → Decidable (_≡_ {A = K}) → (S → K) → (V → K) → BiGUL F Sᵁ Vᵁ → (V → S) →
            BiGUL F (var zero) (var (suc zero)) → BiGUL F (var zero) (var (suc zero))
keyAlignᴮ keq ks kv b c rec = case
  (((λ { []ᴹ []ᴹ → true; _ _ → false }) ,
    normal
      (rearrV (con (left (k tt))) (k {G = one} tt) tt (return refl)
         (skip (const tt)))
      (λ { []ᴹ → true; _ → false })) ∷
   (headMatch keq ks kv ,
    normal
      (rearrS (con (right (prod var var))) (prod var var) (inj₁ refl , inj₂ refl) (return refl >>= return refl)
         (rearrV (con (right (prod var var))) (prod var var) ((inj₁ refl , inj₂ refl)) (return refl >>= return refl)
            (prod b rec)))
      (λ { (_ ∷ᴹ _) → true; _ → false })) ∷
   ((λ { (_ ∷ᴹ _) []ᴹ → true ; _ _ → false }) ,
    adaptive (λ _ _ → []ᴹ)) ∷
   ((λ { ss (v ∷ᴹ _) → ⌊ Any.any (λ s → keq (ks s) (kv v)) (toList₀ ss) ⌋; _ _ → false }) ,
    adaptive (λ { ss (v ∷ᴹ _) → extract keq ks kv v ss; ss _ → ss })) ∷
   ((λ { _ (_ ∷ᴹ _) → true; _ _ → false }) ,
    adaptive (λ { ss (v ∷ᴹ _) → c v ∷ᴹ ss; ss _ → ss } )) ∷ [])

data Elementwise {A B C : Set} (R : ℙ (A × B × C)) : ℙ (List A × List B × List C) where
  []  : Elementwise R ([] , [] , [])
  _∷_ : {x : A} {y : B} {z : C} → R (x , y , z) →
        {xs : List A} {ys : List B} {zs : List C} → Elementwise R (xs , ys , zs) →
        Elementwise R (x ∷ xs , y ∷ ys , z ∷ zs)

data Count {A : Set} (P : ℙ A) : ℙ (ℕ × List A) where
  []   : Count P (zero , [])
  _∷ʸ_ : {x : A} →   P x → {n : ℕ} {xs : List A} → Count P (n , xs) → Count P (suc n , x ∷ xs)
  _∷ⁿ_ : {x : A} → ¬ P x → {n : ℕ} {xs : List A} → Count P (n , xs) → Count P (    n , x ∷ xs)

Post : {K : Set} → (S → K) → (V → K) → ℙ (S × S × V) → ℙ (ListS × ListS × ListV)
Post ks kv R' (ss' , ss , vs) = 
  Σ[ ssᴹ ∈ List S ]
    Elementwise (λ { (s' , s , v) → R' (s' , s , v) × ks s' ≡ kv v }) (toList₀ ss' , ssᴹ , toList₁ vs) ×
    ((s : S) (i : Any (s ≡_) (toList₀ ss))
     (m : ℕ) → Count ((ks s ≡_) ∘ ks) (m , take (toℕ (index i)) (toList₀ ss)) →
     (n : ℕ) → Count ((ks s ≡_) ∘ kv) (n , toList₁ vs) →
     m < n → Any (s ≡_) ssᴹ)

extract-reentry :
  {K : Set} (keq : Decidable (_≡_ {A = K})) (ks : S → K) (kv : V → K) (ss : ListS) (v : V) (vs : ListV) →
  Any (λ s → ks s ≡ kv v) (toList₀ ss) → headMatch keq ks kv (extract keq ks kv v ss) (v ∷ᴹ vs) ≡ true
extract-reentry keq ks kv []ᴹ       v vs ()
extract-reentry keq ks kv (s ∷ᴹ ss) v vs i                with keq (ks s) (kv v)
extract-reentry keq ks kv (s ∷ᴹ ss) v vs i                | yes ks-s≡kv-v = trueFromWitness ks-s≡kv-v
extract-reentry keq ks kv (s ∷ᴹ ss) v vs (here ks-s≡kv-v) | no  ks-s≢kv-v with ks-s≢kv-v ks-s≡kv-v
extract-reentry keq ks kv (s ∷ᴹ ss) v vs (here ks-s≡kv-v) | no  ks-s≢kv-v | ()
extract-reentry keq ks kv (s ∷ᴹ ss) v vs (there i       ) | no  ks-s≢kv-v with extract-reentry keq ks kv ss v vs i
extract-reentry keq ks kv (s ∷ᴹ ss) v vs (there i       ) | no  ks-s≢kv-v | rec with extract keq ks kv v ss
extract-reentry keq ks kv (s ∷ᴹ ss) v vs (there i       ) | no  ks-s≢kv-v | ()  | []ᴹ
extract-reentry keq ks kv (s ∷ᴹ ss) v vs (there i       ) | no  ks-s≢kv-v | rec | s' ∷ᴹ ss' = rec

extract-reindex : 
  {K : Set} (keq : Decidable (_≡_ {A = K})) (ks : S → K) (kv : V → K) (ss : ListS) (v : V) (s* : S) →
  Any (s* ≡_) (toList₀ ss) → Any (s* ≡_) (toList₀ (extract keq ks kv v ss))
extract-reindex keq ks kv []ᴹ       v s*  ()
extract-reindex keq ks kv (s ∷ᴹ ss) v s*  i           with keq (ks s) (kv v)
extract-reindex keq ks kv (s ∷ᴹ ss) v s*  i           | yes ks-s≡kv-v = i
extract-reindex keq ks kv (s ∷ᴹ ss) v .s  (here refl) | no  ks-s≢kv-v with extract keq ks kv v ss
extract-reindex keq ks kv (s ∷ᴹ ss) v .s  (here refl) | no  ks-s≢kv-v | []ᴹ       = here refl
extract-reindex keq ks kv (s ∷ᴹ ss) v .s  (here refl) | no  ks-s≢kv-v | s' ∷ᴹ ss' = there (here refl)
extract-reindex keq ks kv (s ∷ᴹ ss) v s*  (there i  ) | no  ks-s≢kv-v with extract-reindex keq ks kv ss v s* i
extract-reindex keq ks kv (s ∷ᴹ ss) v s*  (there i  ) | no  ks-s≢kv-v | rec with extract keq ks kv v ss
extract-reindex keq ks kv (s ∷ᴹ ss) v s*  (there i  ) | no  ks-s≢kv-v | ()  | []ᴹ
extract-reindex keq ks kv (s ∷ᴹ ss) v .s' (there i  ) | no  ks-s≢kv-v | (here refl) | s' ∷ᴹ ss' = here refl
extract-reindex keq ks kv (s ∷ᴹ ss) v s*  (there i  ) | no  ks-s≢kv-v | (there j  ) | s' ∷ᴹ ss' = there (there j)

extract-head :
  {K : Set} (keq : Decidable (_≡_ {A = K})) (ks : S → K) (kv : V → K) (ss : ListS) (v : V) →
  Any ((_≡ kv v) ∘ ks) (toList₀ ss) → Σ (S × ListS) λ { (s' , ss') → extract keq ks kv v ss ≡ s' ∷ᴹ ss' × ks s' ≡ kv v }
extract-head keq ks kv []ᴹ       v () 
extract-head keq ks kv (s ∷ᴹ ss) v i                with keq (ks s) (kv v)
extract-head keq ks kv (s ∷ᴹ ss) v i                | yes ks-s≡kv-v = (s , ss) , refl , ks-s≡kv-v
extract-head keq ks kv (s ∷ᴹ ss) v (here ks-s≡kv-v) | no  ks-s≢kv-v with ks-s≢kv-v ks-s≡kv-v
extract-head keq ks kv (s ∷ᴹ ss) v (here ks-s≡kv-v) | no  ks-s≢kv-v | ()
extract-head keq ks kv (s ∷ᴹ ss) v (there i)        | no  ks-s≢kv-v with extract-head keq ks kv ss v i
extract-head keq ks kv (s ∷ᴹ ss) v (there i)        | no  ks-s≢kv-v | rec             with extract keq ks kv v ss
extract-head keq ks kv (s ∷ᴹ ss) v (there i)        | no  ks-s≢kv-v | (_ , () , _)    | []ᴹ
extract-head keq ks kv (s ∷ᴹ ss) v (there i)        | no  ks-s≢kv-v | (_ , refl , eq) | s' ∷ᴹ ss' = _ , refl , eq

extract-Count : 
  {K : Set} (keq : Decidable (_≡_ {A = K})) (ks : S → K) (kv : V → K) (ss : ListS) (v : V) →
  Any ((_≡ kv v) ∘ ks) (toList₀ ss) → (s* : S) (i : Any (s* ≡_) (toList₀ ss)) {m : ℕ} →
  Count (λ s → ks s* ≡ ks s) (m , take (toℕ (index i)) (toList₀ ss)) →
  Count (λ s → ks s* ≡ ks s) (m , take (toℕ (index (extract-reindex keq ks kv ss v s* i)))
                                       (toList₀ (extract keq ks kv v ss)))
extract-Count keq ks kv []ᴹ       v e                s* ()          c
extract-Count keq ks kv (s ∷ᴹ ss) v e                s* i           c with keq (ks s) (kv v)
extract-Count keq ks kv (s ∷ᴹ ss) v e                s* i           c | yes ks-s≡kv-v = c
extract-Count keq ks kv (s ∷ᴹ ss) v (here ks-s≡kv-v) s* i           c | no  ks-s≢kv-v with ks-s≢kv-v ks-s≡kv-v
extract-Count keq ks kv (s ∷ᴹ ss) v (here ks-s≡kv-v) s* i           c | no  ks-s≢kv-v | ()
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* i           c | no  ks-s≢kv-v
  with extract-head keq ks kv ss v e
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        .s (here refl) c | no  ks-s≢kv-v
  | h with extract keq ks kv v ss
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        .s (here refl) c | no  ks-s≢kv-v
  | h | []ᴹ       = c
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        .s (here refl) c | no  ks-s≢kv-v
  | ._ , refl , ks-s'≡kv-v | s' ∷ᴹ ss' = (λ ks-s≡ks-s' → ks-s≢kv-v (trans ks-s≡ks-s' ks-s'≡kv-v)) ∷ⁿ c
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≡ks-s ∷ʸ c) | no  ks-s≢kv-v
  | h with extract-Count keq ks kv ss v e s* i c
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≡ks-s ∷ʸ c) | no  ks-s≢kv-v
  | h | rec with extract-reindex keq ks kv ss v s* i
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≡ks-s ∷ʸ c) | no  ks-s≢kv-v
  | h | rec | j with extract keq ks kv v ss
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≡ks-s ∷ʸ c) | no  ks-s≢kv-v
  | h | rec | () | []ᴹ
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≡ks-s ∷ʸ c) | no  ks-s≢kv-v
  | ._ , refl , ks-s'≡kv-v | rec | here refl | s' ∷ᴹ ss' with ks-s≢kv-v (trans (sym ks-s*≡ks-s) ks-s'≡kv-v)
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≡ks-s ∷ʸ c) | no  ks-s≢kv-v
  | ._ , refl , ks-s'≡kv-v | rec | here refl | s' ∷ᴹ ss' | ()
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≡ks-s ∷ʸ c) | no  ks-s≢kv-v
  | ._ , refl , ks-s'≡kv-v | ks-s*≡ks-s' ∷ʸ c' | there j | s' ∷ᴹ ss' = ks-s*≡ks-s' ∷ʸ (ks-s*≡ks-s ∷ʸ c')
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≡ks-s ∷ʸ c) | no  ks-s≢kv-v
  | ._ , refl , ks-s'≡kv-v | ks-s*≢ks-s' ∷ⁿ c' | there j | s' ∷ᴹ ss' = ks-s*≢ks-s' ∷ⁿ (ks-s*≡ks-s ∷ʸ c')
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≢ks-s ∷ⁿ c) | no  ks-s≢kv-v
  | h with extract-Count keq ks kv ss v e s* i c
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≢ks-s ∷ⁿ c) | no  ks-s≢kv-v
  | h | rec with extract-reindex keq ks kv ss v s* i
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≢ks-s ∷ⁿ c) | no  ks-s≢kv-v
  | h | rec | j with extract keq ks kv v ss
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≢ks-s ∷ⁿ c) | no  ks-s≢kv-v
  | h | rec | () | []ᴹ
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≢ks-s ∷ⁿ c) | no  ks-s≢kv-v
  | ._ , refl , ks-s'≡kv-v | rec | here refl | s' ∷ᴹ ss' = rec
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≢ks-s ∷ⁿ c) | no  ks-s≢kv-v
  | ._ , refl , ks-s'≡kv-v | ks-s*≡ks-s' ∷ʸ c' | there j | s' ∷ᴹ ss' = ks-s*≡ks-s' ∷ʸ (ks-s*≢ks-s ∷ⁿ c')
extract-Count keq ks kv (s ∷ᴹ ss) v (there e)        s* (there i  ) (ks-s*≢ks-s ∷ⁿ c) | no  ks-s≢kv-v
  | ._ , refl , ks-s'≡kv-v | ks-s*≢ks-s' ∷ⁿ c' | there j | s' ∷ᴹ ss' = ks-s*≢ks-s' ∷ⁿ (ks-s*≢ks-s ∷ⁿ c')

keyAlign-correctness :
  {K : Set} (keq : Decidable (_≡_ {A = K})) (ks : S → K) (kv : V → K) (b : BiGUL F Sᵁ Vᵁ) (c : V → S)
  (R' : ℙ (S × S × V)) → Triple (λ { (s , v) → ks s ≡ kv v }) b (R' ∩ (λ { (s' , _ , v) → ks s' ≡ kv v })) →
  ((v : V) → ks (c v) ≡ kv v) →
  (n : ℕ) (rec : BiGUL F (var zero) (var (suc zero))) →
  ({m : ℕ} → Triple (((_≡ m) ∘ length ∘ toList₁ ∘ proj₂) ∩ (λ _ → m < n)) rec (Post ks kv R')) →
  Triple ((_≡ n) ∘ length ∘ toList₁ ∘ proj₂) (keyAlignᴮ keq ks kv b c rec) (Post ks kv R')
keyAlign-correctness keq ks kv b c R' b-t c-eq n rec rec-t =
  case
    (conseq (λ { {[]ᴹ    , []ᴹ   } _ → tt , tt , refl
               ; {[]ᴹ    , _ ∷ᴹ _} (_ , () , _)
               ; {_ ∷ᴹ _ , []ᴹ   } (_ , () , _)
               ; {_ ∷ᴹ _ , _ ∷ᴹ _} (_ , () , _) })
            (rearrV (λ { ([]ᴹ , _) → ⊤; (_ ∷ᴹ _ , _) → ⊥ }) (λ { ([]ᴹ , _) → ⊤; (_ ∷ᴹ _ , _) → ⊥ })
               (conseq (λ _ → refl)
                       skip
                       (λ { { .[]ᴹ   , []ᴹ    , _} (refl , _) → tt , tt , refl
                          ; {  []ᴹ   , _ ∷ᴹ _ , _} _ → tt , tt , refl
                          ; { _ ∷ᴹ _ , _ ∷ᴹ _ , _} (_ , _ , () , _) })))
            (λ { {[]ᴹ    , []ᴹ    , []ᴹ   } _ → ([] , [] , λ _ ()) , (refl , tt) , refl , tt
               ; {_ ∷ᴹ _ , []ᴹ    , []ᴹ   } ((_ , () , _) , _)
               ; {_      , []ᴹ    , _ ∷ᴹ _} (_ , _ , () , _)
               ; {_      , _ ∷ᴹ _ , []ᴹ   } (_ , _ , () , _)
               ; {_      , _ ∷ᴹ _ , _ ∷ᴹ _} (_ , _ , () , _) }) ∷ᴺ
     conseq
       (λ { {[]ᴹ    , []ᴹ   } (_ , () , _)
          ; {[]ᴹ    , _ ∷ᴹ _} (_ , () , _)
          ; {_ ∷ᴹ _ , []ᴹ   } (_ , () , _)
          ; {_ ∷ᴹ _ , _ ∷ᴹ _} (vlen , eqn , _) → _ , (refl , refl) , vlen , trueToWitness eqn })
       (rearrS (λ { ((s , ss) , []ᴹ    ) → ⊥
                  ; ((s , ss) , v ∷ᴹ vs) → length (toList₁ (v ∷ᴹ vs)) ≡ n × ks s ≡ kv v })
               (Post ks kv R' ∘ Product.map (uncurry _∷ᴹ_) (Product.map (uncurry _∷ᴹ_) id))
          (conseq
             (λ { {_ , []ᴹ   } (_ , _ , ())
                ; {_ , _ ∷ᴹ _} (_ , (refl , refl) , vlen , ks-s≡kv-v) → _ , (vlen , ks-s≡kv-v) , refl , refl })
             (rearrV (λ { ((s , ss) , (v , vs)) → length (toList₁ (v ∷ᴹ vs)) ≡ n × ks s ≡ kv v })
                     (Post ks kv R' ∘ Product.map (uncurry _∷ᴹ_) (Product.map (uncurry _∷ᴹ_) (uncurry _∷ᴹ_)))
                (conseq
                   (λ { (_ , (vlen , ks-s≡kv-v) , eq , vseq) → 
                        trans ks-s≡kv-v (cong kv eq) ,
                        cong pred (subst (λ vs → suc (length (toList₁ vs)) ≡ n) vseq vlen) , pred-lemma vlen })
                   (prod b-t rec-t)
                   (λ { {(s' , ss') , (s , ss) , (v , vs)}
                        (((R'-s'-s-v , ks-s'≡kv-v) , (ssᴹ , ew , ret)) , (v' , vs') , (_ , ks-s≡kv-v') , v'≡v , vs'≡vs) →
                          _ , (s ∷ ssᴹ , (R'-s'-s-v , ks-s'≡kv-v) ∷ ew ,
                               λ { sᴹ (here eq) m cm n cn m<n → here eq
                                 ; sᴹ (there i) (suc m) (ks-sᴹ≡ks-s ∷ʸ cm) (suc n) (ks-sᴹ≡kv-v ∷ʸ cn) (s≤s m<n) →
                                     there (ret sᴹ i m cm n cn m<n)
                                 ; sᴹ (there i) m (ks-sᴹ≡ks-s ∷ʸ cm) n (ks-sᴹ≢kv-v ∷ⁿ cn) m<n →
                                     ⊥-elim (ks-sᴹ≢kv-v (trans ks-sᴹ≡ks-s (trans ks-s≡kv-v' (cong kv v'≡v))))
                                 ; sᴹ (there i) m (ks-sᴹ≢ks-s ∷ⁿ cm) n (ks-sᴹ≡kv-v ∷ʸ cn) m<n →
                                     ⊥-elim (ks-sᴹ≢ks-s (trans ks-sᴹ≡kv-v (sym (trans ks-s≡kv-v' (cong kv v'≡v)))))
                                 ; sᴹ (there i) m (ks-sᴹ≢ks-s ∷ⁿ cm) n (ks-sᴹ≢kv-v ∷ⁿ cn) m<n →
                                     there (ret sᴹ i m cm n cn m<n) }) ,
                          refl , refl })))
             (λ { {_ , _ , []ᴹ   } (_ , _ , _ , ())
                ; {_ , _ , _ ∷ᴹ _} ((_ , post , refl , refl) , _ , (refl , refl) , _) →
                    _ , post , (refl , refl) , refl , refl})))
       (λ { {[]ᴹ , _} ((_ , _ , () , _) , _)
          ; {_ ∷ᴹ _ , []ᴹ , _} ((_ , _ , _ , ()) , _)
          ; {_ ∷ᴹ _ , _ ∷ᴹ _ , []ᴹ   } ((_ , _ , (refl , refl) , (refl , refl)) , _ , () , _)
          ; {_ ∷ᴹ _ , _ ∷ᴹ _ , _ ∷ᴹ _} ((_ , ([] , () , _) , _) , _)
          ; {_ ∷ᴹ _ , _ ∷ᴹ _ , _ ∷ᴹ _} ((_ , (sᴹ ∷ ssᴹ , (r' , ks-s'≡kv-v) ∷ ew , r) , (refl , refl) , (refl , refl)) , _) →
              (sᴹ ∷ ssᴹ , (r' , ks-s'≡kv-v) ∷ ew , r) , (trueFromWitness ks-s'≡kv-v , refl , tt) , refl , refl , tt }) ∷ᴺ
     (λ { []ᴹ      []ᴹ      (_ , () , _)
        ; []ᴹ      (_ ∷ᴹ _) (_ , () , _)
        ; (_ ∷ᴹ _) []ᴹ      (vlen , _) →
            (vlen , inj₁ refl) ,
            (λ { []ᴹ      _ → [] , [] , λ { sᴹ i m cm (suc n) () (s≤s m≤n) }
               ; (_ ∷ᴹ _) (_ , () , _) })
        ; (_ ∷ᴹ _) (_ ∷ᴹ _) (_ , () , _) }) ∷ᴬ
     (λ { _         []ᴹ       (_ , () , _)
        ; []ᴹ       (_ ∷ᴹ _)  (vlen , () , _)
        ; (s ∷ᴹ ss) (v ∷ᴹ vs) (vlen , anyeqn , _ , ks-s≢kv-v , _) →
            (vlen , inj₂ (inj₁ (extract-reentry keq ks kv (s ∷ᴹ ss) v vs (trueToWitness anyeqn)))) ,
            λ { ss' (ssᴹ , ew , ret) →
                  ssᴹ , ew ,
                  λ s* i m cm n cn m<n →
                      ret s* (extract-reindex keq ks kv (s ∷ᴹ ss) v s* i) m
                             (extract-Count keq ks kv (s ∷ᴹ ss) v (trueToWitness anyeqn) s* i cm) n cn m<n } }) ∷ᴬ
     (λ { ss []ᴹ       (_ , () , _)
        ; ss (v ∷ᴹ vs) (vlen , _ , ¬any , _) →
            (vlen , inj₂ (inj₁ (trueFromWitness (c-eq v)))) ,
            λ { []ᴹ         (_ , () , _)
              ; (s' ∷ᴹ ss') (ssᴹ , ew , ret) →
                  ssᴹ , ew ,
                  λ s i m cm n cn m<n →
                    ret s (there i) m
                        ((λ ks-s≡ks-c-v →
                              falseToWitness ¬any
                                (Any.map (λ s≡x → trans (cong ks (sym s≡x)) (trans ks-s≡ks-c-v (c-eq v))) i)) ∷ⁿ cm)
                        n cn m<n } }) ∷ᴬ [])
    (λ { {[]ᴹ    , []ᴹ   } _ → inj₁ refl
       ; {_ ∷ᴹ _ , []ᴹ   } _ → inj₂ (inj₂ (inj₁ refl))
       ; {_      , _ ∷ᴹ _} _ → inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) })

keyAlign-finite-expansion :
  {K : Set} (keq : Decidable (_≡_ {A = K})) (ks : S → K) (kv : V → K) (b : BiGUL F Sᵁ Vᵁ) (c : V → S)
  (R' : ℙ (S × S × V)) → Triple (λ { (s , v) → ks s ≡ kv v }) b (R' ∩ (λ { (s' , _ , v) → ks s' ≡ kv v })) →
  ((v : V) → ks (c v) ≡ kv v) →
  (l n : ℕ) → n ≤ l → Triple ((_≡ n) ∘ length ∘ toList₁ ∘ proj₂)
                             (expand (suc l) (keyAlignᴮ keq ks kv b c))
                             (Post ks kv R')
keyAlign-finite-expansion keq ks kv b c R' b-t c-eq l n n≤l =
  conseq (_,_ tt)
         (expandTriple (keyAlignᴮ keq ks kv b c) (length ∘ toList₁ ∘ proj₂) Π (Post ks kv R')
                       (λ n rec rec-t → conseq proj₂
                                               (keyAlign-correctness keq ks kv b c R' b-t c-eq n rec
                                                  (conseq (_,_ tt) rec-t proj₁))
                                               proj₁)
                       l n n≤l)
         proj₁

keyAlign-range :
  {K : Set} (keq : Decidable (_≡_ {A = K})) (ks : S → K) (kv : V → K) (b : BiGUL F Sᵁ Vᵁ) (c : V → S) →
  TripleR (λ { (s , v) → ks s ≡ kv v }) b Π →
  ((v : V) → ks (c v) ≡ kv v) →
  (n : ℕ) (rec : BiGUL F (var zero) (var (suc zero))) →
  ({m : ℕ} → TripleR (((_≡ m) ∘ length ∘ toList₁ ∘ proj₂)) rec
                     (((_≡ m) ∘ length ∘ toList₀) ∩ (λ _ → m < n))) →
  TripleR ((_≡ n) ∘ length ∘ toList₁ ∘ proj₂) (keyAlignᴮ keq ks kv b c rec) ((_≡ n) ∘ length ∘ toList₀)
keyAlign-range keq ks kv b c b-t c-eq n rec rec-t =
  conseq
    proj₁
    (case
       ((conseq
           (λ { {[]ᴹ    , []ᴹ   } (_ , 0≡n) → 0≡n , refl , tt
              ; {[]ᴹ    , _ ∷ᴹ _} ((_ , _ , ()) , _)
              ; {_ ∷ᴹ _ , []ᴹ   } (_ , ())
              ; {_ ∷ᴹ _ , _ ∷ᴹ _} (_ , ()) })
           (rearrV
              (λ { ([]ᴹ , tt) → 0 ≡ n ; (_ ∷ᴹ _ , tt) → ⊥ })
              (conseq {Q = λ { []ᴹ → 0 ≡ n; (_ ∷ᴹ _) → ⊥ }}
                 (λ { {[]ᴹ    , tt} (_ , 0≡n) → tt , 0≡n , refl
                    ; {_ ∷ᴹ _ , tt} (_ , ()) })
                 skip
                 (λ _ → tt)))
           id) ∷ᴺ
        (conseq {Q = λ { []ᴹ → ⊥; (_ ∷ᴹ ss) → suc (length (toList₀ ss)) ≡ n }}
           (λ { {[]ᴹ     , []ᴹ    } (_ , ())
              ; {[]ᴹ     , _ ∷ᴹ _ } (_ , ())
              ; {_ ∷ᴹ _  , []ᴹ    } ((_ , _ , ()) , _)
              ; {s ∷ᴹ ss , v ∷ᴹ vs} ((_ , (refl , refl) , ks-s≡kv-v , suc-len-vs≡n) , suc-len-ss≡n) →
                suc-len-vs≡n , trueFromWitness ks-s≡kv-v , refl , tt })
           (rearrS
              (λ { ((s , _) , []ᴹ    ) → ⊥
                 ; ((s , _) , v ∷ᴹ vs) → ks s ≡ kv v × suc (length (toList₁ vs)) ≡ n})
              (λ { (_ , ss) → length (toList₀ ss) ≡ pred n × pred n < n })
              (conseq
                 (λ { {(s , ss) , []ᴹ} ((_ , _ , ()) , _)
                    ; {(s , ss) , v ∷ᴹ vs} ((_ , (ks-s≡kv-v , suc-len-vs≡n) , refl , refl) ,
                                            (_ , (suc-len-ss≡pred-n , pred-n<n) , refl , refl)) →
                      (s , ss) , (refl , refl) , ks-s≡kv-v , suc-len-vs≡n })
                 (rearrV
                    (λ { ((s , _) , (v , vs)) → ks s ≡ kv v × suc (length (toList₁ vs)) ≡ n })
                    (conseq 
                       (λ { {(s , ss) , (v , vs)} ((ks-s≡kv-v , len-vs≡pred-n) , len-ss≡pred-n , pred-n<n) →
                            (v , vs) , (ks-s≡kv-v , trans (cong suc len-vs≡pred-n) (pred-inverse-lemma pred-n<n)) ,
                            refl , refl })
                       (prod b-t (rec-t {pred n}))
                       (_,_ tt)))
                 (λ { {s' , ss'} ((s , ss) , (len-ss≡pred-n , pred-n<n) , s≡s' , ss≡ss') →
                      trans (cong (length ∘ toList₀) (sym ss≡ss')) len-ss≡pred-n , pred-n<n })))
           (λ { {[]ᴹ} ()
              ; {s ∷ᴹ ss} suc-len-ss≡n →
                  (s , ss) , (cong pred suc-len-ss≡n , pred-lemma suc-len-ss≡n) , refl , refl })) ∷ᴺ •∷ᴬ •∷ᴬ •∷ᴬ []))
    (λ { {[]ᴹ   } → inj₁ ∘ (_, (refl , tt))
       ; {_ ∷ᴹ _} → inj₂ ∘ inj₁ ∘ (_, (refl , refl , tt)) })

keyAlign-finite-expansionR :
  {K : Set} (keq : Decidable (_≡_ {A = K})) (ks : S → K) (kv : V → K) (b : BiGUL F Sᵁ Vᵁ) (c : V → S) →
  TripleR (λ { (s , v) → ks s ≡ kv v }) b Π → ((v : V) → ks (c v) ≡ kv v) →
  (l n : ℕ) → n ≤ l → TripleR ((_≡ n) ∘ length ∘ toList₁ ∘ proj₂)
                              (expand (suc l) (keyAlignᴮ keq ks kv b c))
                              ((_≡ n) ∘ length ∘ toList₀)
keyAlign-finite-expansionR keq ks kv b c b-t c-eq l n n≤l =
  conseq
    (proj₂ ∘ proj₁)
    (expandTripleR (keyAlignᴮ keq ks kv b c) (length ∘ toList₁ ∘ proj₂) Π (λ n → (_≡ n) ∘ length ∘ toList₀)
       (λ n rec rec-t →
          conseq
            ((_,_ tt) ∘ proj₁)
            (keyAlign-range keq ks kv b c b-t c-eq n rec (conseq (proj₂ ∘ proj₁) rec-t id))
            id)
       l n n≤l)
    id
