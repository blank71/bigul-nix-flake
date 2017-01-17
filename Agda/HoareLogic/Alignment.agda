open import DynamicallyChecked.Universe
open import Data.Nat as Nat

module HoareLogic.Alignment (Sᵁ Vᵁ : {n : ℕ} → U n) where

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

isNil₀ : (ss : ListS) → Dec (ss ≡ []ᴹ)
isNil₀ ss = U-dec (var zero) ss []ᴹ

isCons₀ : (ss : ListS) → Dec (Σ[ ht ∈ (S × ListS) ] ss ≡ con (inj₂ ht))
isCons₀ (con (inj₁ _ )) = no (λ { (_ , ()) })
isCons₀ (con (inj₂ ht)) = yes (ht , refl)

toList₀ : ListS → List S
toList₀ []ᴹ       = []
toList₀ (s ∷ᴹ ss) = s ∷ toList₀ ss

isNil₁ : (vs : ListV) → Dec (vs ≡ []ᴹ)
isNil₁ vs = U-dec (var (suc zero)) vs []ᴹ

isCons₁ : (vs : ListV) → Dec (Σ[ ht ∈ (V × ListV) ] vs ≡ con (inj₂ ht))
isCons₁ (con (inj₁ _ )) = no (λ { (_ , ()) })
isCons₁ (con (inj₂ ht)) = yes (ht , refl)

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

keyAlignᴮ : {K : Set} → Decidable (_≡_ {A = K}) → (S → K) → (V → K) → BiGUL F Sᵁ Vᵁ → (V → S) →
            BiGUL F (var zero) (var (suc zero)) → BiGUL F (var zero) (var (suc zero))
keyAlignᴮ keq ks kv b c rec = case
  (((λ { []ᴹ []ᴹ → true; _ _ → false }) ,
    normal
      (rearrV (con (left (k tt))) (k {G = one} tt) tt (return refl)
         (skip (const tt)))
      (λ { []ᴹ → true; _ → false })) ∷
   ((λ { (s ∷ᴹ _) (v ∷ᴹ _) → ⌊ keq (ks s) (kv v) ⌋ ; _ _ → false }) ,
    normal
      (rearrS (con (right (prod var var))) (prod var var) (inj₁ refl , inj₂ refl) (return refl >>= return refl)
         (rearrV (con (right (prod var var))) (prod var var) ((inj₁ refl , inj₂ refl)) (return refl >>= return refl)
            (prod b rec)))
      (λ { (_ ∷ᴹ _) → true; _ → false })) ∷
   ((λ { (_ ∷ᴹ _) []ᴹ → true ; _ _ → false }) ,
    adaptive (λ _ _ → []ᴹ)) ∷
   ((λ { ss (v ∷ᴹ _) → ⌊ Any.any (keq (kv v)) (List.map ks (toList₀ ss)) ⌋; _ _ → false }) ,
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

pred-lemma : {m n : ℕ} → suc m ≡ n → pred n < n
pred-lemma refl = DecTotalOrder.refl Nat.decTotalOrder

keyAlign-correctness :
  {K : Set} (keq : Decidable (_≡_ {A = K})) (ks : S → K) (kv : V → K) (b : BiGUL F Sᵁ Vᵁ) (c : V → S)
  (R' : ℙ (S × S × V)) → Triple Π b (R' ∩ (λ { (s' , _ , v) → ks s' ≡ kv v })) → ((v : V) → ks (c v) ≡ kv v) →
  (n : ℕ) (rec : BiGUL F (var zero) (var (suc zero))) →
  ({m : ℕ} → Triple (((_≡ m) ∘ length ∘ toList₁ ∘ proj₂) ∩ (λ _ → m < n)) rec (Post ks kv R')) →
  Triple ((_≡ n) ∘ length ∘ toList₁ ∘ proj₂) (keyAlignᴮ keq ks kv b c rec) (Post ks kv R')
keyAlign-correctness keq ks kv b c R' b-t c-eq n rec rec-t =
  case
    ((conseq (λ { {[]ᴹ    , []ᴹ   } _ → tt , tt , refl
                ; {[]ᴹ    , _ ∷ᴹ _} (_ , () , _)
                ; {_ ∷ᴹ _ , []ᴹ   } (_ , () , _)
                ; {_ ∷ᴹ _ , _ ∷ᴹ _} (_ , () , _) })
             (rearrV (λ { ([]ᴹ , _) → ⊤; (_ ∷ᴹ _ , _) → ⊥ }) (λ { ([]ᴹ , _) → ⊤; (_ ∷ᴹ _ , _) → ⊥ })
                (conseq (λ _ → refl)
                        skip
                        (λ { { .[]ᴹ   , []ᴹ    , _} (refl , _) → tt , tt , refl
                           ; {  []ᴹ   , _ ∷ᴹ _ , _} _ → tt , tt , refl
                           ; { _ ∷ᴹ _ , _ ∷ᴹ _ , _} (_ , _ , () , _) })))
             (λ { {[]ᴹ    , []ᴹ    , []ᴹ   } _ → ([] , [] , λ _ ()) , (refl , tt) , refl
                ; {_ ∷ᴹ _ , []ᴹ    , []ᴹ   } ((_ , () , _) , _)
                ; {_      , []ᴹ    , _ ∷ᴹ _} (_ , _ , () , _)
                ; {_      , _ ∷ᴹ _ , []ᴹ   } (_ , _ , () , _)
                ; {_      , _ ∷ᴹ _ , _ ∷ᴹ _} (_ , _ , () , _) }) ,
      λ _ → tt) ∷ᴺ
     (conseq
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
                    (λ { (_ , (vlen , ks-s≡kv-v) , _ , vseq) → 
                         tt , cong pred (subst (λ vs → suc (length (toList₁ vs)) ≡ n) vseq vlen) , pred-lemma vlen })
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
               (sᴹ ∷ ssᴹ , (r' , ks-s'≡kv-v) ∷ ew , r) , (trueFromWitness ks-s'≡kv-v , refl , tt) , refl }) ,
      (λ { {[]ᴹ    } ()
         ; {s ∷ᴹ ss} _ → refl , tt })) ∷ᴺ
     ((λ { {[]ᴹ    , []ᴹ   } (_ , () , _)
         ; {[]ᴹ    , _ ∷ᴹ _} (_ , () , _)
         ; {_ ∷ᴹ _ , []ᴹ   } (vlen , _) → vlen , inj₁ refl
         ; {_ ∷ᴹ _ , _ ∷ᴹ _} (_ , () , _) }) ,
      (λ { {_ , []ᴹ    , []ᴹ   } ((_ , () , _) , _)
         ; {_ , []ᴹ    , _ ∷ᴹ _} ((_ , () , _) , _)
         ; {[]ᴹ    , _ ∷ᴹ _ , []ᴹ   } _ → {!!}
         ; {_ ∷ᴹ _ , _ ∷ᴹ _ , []ᴹ   } → {!!}
         ; {_ , _ ∷ᴹ _ , _ ∷ᴹ _} ((_ , () , _) , _) })) ∷ᴬ
     ({!!} ,
      {!!}) ∷ᴬ
     ((λ { {_ , []ᴹ   } (_ , () , _)
         ; {_ , v ∷ᴹ _} (vlen , rest) → vlen , inj₂ (inj₁ (trueFromWitness (c-eq v))) }) ,
      {!!}) ∷ᴬ [])
    (λ { {[]ᴹ    , []ᴹ   } _ → inj₁ refl
       ; {_ ∷ᴹ _ , []ᴹ   } _ → inj₂ (inj₂ (inj₁ refl))
       ; {_      , _ ∷ᴹ _} _ → inj₂ (inj₂ (inj₂ (inj₂ (inj₁ refl)))) })

keyAlign-finite-expansion :
  {K : Set} (keq : Decidable (_≡_ {A = K})) (ks : S → K) (kv : V → K) (b : BiGUL F Sᵁ Vᵁ) (c : V → S)
  (R' : ℙ (S × S × V)) → Triple Π b (R' ∩ (λ { (s' , _ , v) → ks s' ≡ kv v })) → ((v : V) → ks (c v) ≡ kv v) →
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

{-

λ { {[]ᴹ    , []ᴹ   } → ?
  ; {[]ᴹ    , _ ∷ᴹ _} → ?
  ; {_ ∷ᴹ _ , []ᴹ   } → ?
  ; {_ ∷ᴹ _ , _ ∷ᴹ _} → ? }

λ { {_ , []ᴹ    , []ᴹ   } → ?
  ; {_ , []ᴹ    , _ ∷ᴹ _} → ?
  ; {_ , _ ∷ᴹ _ , []ᴹ   } → ?
  ; {_ , _ ∷ᴹ _ , _ ∷ᴹ _} → ? }

λ { {[]ᴹ    , []ᴹ    , []ᴹ   } → ?
  ; {[]ᴹ    , []ᴹ    , _ ∷ᴹ _} → ?
  ; {[]ᴹ    , _ ∷ᴹ _ , []ᴹ   } → ?
  ; {[]ᴹ    , _ ∷ᴹ _ , _ ∷ᴹ _} → ?
  ; {_ ∷ᴹ _ , []ᴹ    , []ᴹ   } → ?
  ; {_ ∷ᴹ _ , []ᴹ    , _ ∷ᴹ _} → ?
  ; {_ ∷ᴹ _ , _ ∷ᴹ _ , []ᴹ   } → ?
  ; {_ ∷ᴹ _ , _ ∷ᴹ _ , _ ∷ᴹ _} → ? }

-}
