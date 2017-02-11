module HoareLogic.Examples.Miscellaneous where

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
open import Data.Maybe
open import Data.Nat as Nat
open import Data.Fin
open import Data.List
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
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
                  Triple Π (emb {F = F} {S} {V} g p)
                         (λ { (s' , s , v) → g s' ≡ v × (g s ≡ v → s' ≡ s) × (g s ≢ v → s' ≡ p s v) })
emb-correctness g p PutGet =
  case
    (conseq
       (λ { (_ , eqn , _) → trueToWitness eqn })
       skip
       (λ { {.s , s , v} (refl , _ , eqn , _) →
              (trueToWitness eqn , (λ _ → refl) , (λ g-s≢v → ⊥-elim (g-s≢v (trueToWitness eqn)))) ,
              (eqn , tt) , refl , tt }) ∷ᴺ
     (λ { s v (_ , _ , feqn , _) →
            (tt , inj₁ (trueFromWitness PutGet)) ,
            λ { s' (g-s'≡v , PutGet⇒s'≡p-s-v , _) →
                  g-s'≡v , (λ g-s≡v → ⊥-elim (falseToWitness feqn g-s≡v)) , (λ _ → PutGet⇒s'≡p-s-v PutGet) } }) ∷ᴬ [])
    (λ _ → inj₂ (inj₁ refl))

emb-correctness' : {n : ℕ} {F : Functor n} {S V : U n}
                   (g : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F)) (p : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)) →
                   ({s : ⟦ S ⟧ (μ F)} {v : ⟦ V ⟧ (μ F)} → g (p s v) ≡ v) →
                   ({s : ⟦ S ⟧ (μ F)} → p s (g s) ≡ s) →
                   Triple Π (emb {F = F} {S} {V} g p) (λ { (s' , s , v) → s' ≡ p s v })
emb-correctness' g p PutGet GetPut =
  case
    (conseq
       (λ { (_ , eqn , _) → trueToWitness eqn })
       skip
       (λ { {.s , s , v} (refl , _ , eqn , _) →
            trans (sym GetPut) (cong (p s) (trueToWitness eqn)) , (eqn , tt) , refl , tt }) ∷ᴺ
     (λ { s v (_ , _ , neqn , _) →
          (tt , inj₁ (trueFromWitness PutGet)) ,
          (λ s' eq → trans eq (trans (cong (p (p s v)) (sym PutGet)) GetPut)) }) ∷ᴬ [])
    (λ _ → inj₂ (inj₁ refl))

emb-range : {n : ℕ} {F : Functor n} {S V : U n}
            (g : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F)) (p : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)) →
            TripleR Π (emb {F = F} {S} {V} g p) Π
emb-range g p =
  conseq
    (λ _ → tt)
    (case
       (((conseq
            (λ { (eq , _) → tt , trueFromWitness eq , tt })
            skip
            id) ,
         (λ _ → refl , tt)) ∷ᴺ •∷ᴬ []))
    inj₁


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

keepHeight : BiGUL emptyF (kℕ ⊗ kℕ) kℕ
keepHeight = rearrV var (prod {H = one} var (k tt)) (refl , tt) (return refl) (prod replace (skip (const tt)))

keepHeight-correctness : Triple Π keepHeight (λ { ((w' , h') , (_ , h) , v) → w' ≡ v × h' ≡ h })
keepHeight-correctness =
  conseq
    (λ _ → _ , tt , refl)
    (rearrV Π (λ { ((w' , h') , (_ , h) , v) → w' ≡ v × h' ≡ h })
       (conseq
          (λ _ → tt , refl)
          (prod replace skip)
          (λ { {(.v , .h) , (w , h) , (v , _)} ((refl , refl) , _) → _ , (refl , refl) , refl , refl })))
    (λ { {(w' , .h) , (w , h) , v} ((._ , (eq , refl) , refl) , _) → eq , refl })

keepHeight-range : TripleR Π keepHeight Π
keepHeight-range =
  conseq
    (λ _ → tt)
    (rearrV Π
       (conseq
          (λ _ → _ , tt , refl , refl)
          (prod replace skip)
          (λ { tt → tt , tt })))
    id

makeSquare : BiGUL emptyF (kℕ ⊗ kℕ) kℕ
makeSquare =
  case
    (((λ { (w , _) v → ⌊ w Nat.≟ v ⌋ }) ,
      normal (skip proj₁)
             (const true)) ∷
     (((λ _ _ → true) ,
      adaptive (λ { _ v → (v , v) }))) ∷ [])

makeSquare-correctness :
  Triple Π makeSquare (λ { ((w' , h') , (w , h) , v) → w' ≡ v × (w ≡ v → h' ≡ h) × (w ≢ v → w' ≡ h') })
makeSquare-correctness =
  case
    ((conseq
        (λ { {(w , h) , v} (_ , e , _) → trueToWitness e })
        skip
        (λ { {.(w , h) , (w , h) , v} (refl , _ , e , _) →
             (trueToWitness e , (λ _ → refl) , (λ w≢v → ⊥-elim (w≢v (trueToWitness e)))) , (e , tt) , refl , tt })) ∷ᴺ
     (λ { (w , h) v (tt , _ , ne , _) →
          (tt , inj₁ (trueFromWitness refl)) ,
          λ { (w' , h') (w'≡v , v≡v→h'≡v , _) →
              w'≡v , (λ w≡v → ⊥-elim (falseToWitness ne w≡v)) , (λ _ → trans w'≡v (sym (v≡v→h'≡v refl))) } }) ∷ᴬ [])
    (λ _ → inj₂ (inj₁ refl))

makeSquare-range : TripleR Π makeSquare Π
makeSquare-range =
  conseq
    proj₁
    (case
       ((conseq
           (λ { {(w , h) , v} (w≡v , _) → tt , trueFromWitness w≡v , tt })
           skip
           (λ _ → tt) ,
         (λ _ → refl , tt)) ∷ᴺ •∷ᴬ []))
    inj₁

just-lemma : {A : Set} {x y : A} → (Maybe A ∋ just x) ≡ just y → x ≡ y
just-lemma refl = refl

module _ (Rational : Set) (_≟_ : Decidable (_≡_ {A = Rational}))
         (zero : Rational)
         (mul : Rational → Rational → Rational)
         (div : Rational → (d : Rational) → Maybe Rational)
         (DivNonZero : (x y : Rational) → y ≢ zero → Σ[ z ∈ Rational ] div x y ≡ just z)
         (DivMul : (x y z : Rational) → div x y ≡ just z → mul y z ≡ x)
         (CrossEq : (a b c d : Rational) → mul d a ≡ mul c b → b ≢ zero → d ≢ zero → div a b ≡ div c d) where

  kQ : U 0
  kQ = k Rational _≟_
  
  fromJustOrZero : Maybe Rational → Rational
  fromJustOrZero (just x) = x
  fromJustOrZero nothing  = zero

  keepRatio : BiGUL emptyF (kQ ⊗ kQ) kQ
  keepRatio =
    case
      (((λ { (w , _) _ → ⌊ w ≟ zero ⌋ }) ,
        adaptive λ { (_ , h) v → (v , h) }) ∷
       ((λ { (w , _) v → ⌊ w ≟ v ⌋ }) ,
        normal (skip proj₁) (λ _ → true)) ∷
       ((λ _ _ → true) ,
        adaptive (λ { (w , h) v → (v , fromJustOrZero (div (mul h v) w)) })) ∷ [])

  keepRatio-correctness : Triple (λ { (_ , v) → v ≢ zero }) keepRatio
                                 (λ { ((w' , h') , (w , h) , v) →
                                        w' ≡ v × (w ≡ zero → h' ≡ h) × (w ≢ zero → div h' w' ≡ div h w) })
  keepRatio-correctness =
    case
      ((λ { (w , h) v (v≢zero , w==zero , _) →
            (v≢zero , falseFromWitness v≢zero , inj₁ (trueFromWitness refl)) ,
            (λ { (w' , h') (w'≡v , v≡zero→h'≡h , v≢zero→h'/w'≡h/v) →
                 w'≡v ,
                 (λ w≡zero →
                    let (x , h'/w'≡just-x) = DivNonZero h' w' (subst (_≢ zero) (sym w'≡v) v≢zero)
                        (y , h/v≡just-y)   = DivNonZero h v v≢zero
                    in  trans (sym (DivMul h' w' x h'/w'≡just-x))
                              (trans (trans (subst (λ a → mul w' x ≡ mul a x) w'≡v refl)
                                            (cong (mul v) (just-lemma (trans (sym h'/w'≡just-x)
                                                                             (trans (v≢zero→h'/w'≡h/v v≢zero) h/v≡just-y)))))
                                     (DivMul h v y h/v≡just-y))) ,
                 (λ w≢zero → ⊥-elim (w≢zero (trueToWitness w==zero))) }) }) ∷ᴬ
       conseq
         (λ { {(w , h) , v} (v≢zero , w==v , w/=zero , _) → trueToWitness w==v })
         skip
         (λ { {.(w , h) , (w , h) , v} (refl , v≢zero , w==v , w/=zero , _) →
              (trueToWitness w==v , (λ _ → refl) , (λ _ → refl)) , (w==v , w/=zero , tt) , refl , tt }) ∷ᴺ
       (λ { (w , h) v (v≢zero , _ , w/=v , w/=zero , _) →
            (v≢zero , falseFromWitness v≢zero , inj₁ (trueFromWitness refl)) ,
            (λ { (w' , h') → aux w' h' w h v (falseToWitness w/=zero) v≢zero }) }) ∷ᴬ [])
      (λ _ → inj₂ (inj₂ (inj₁ refl)))
    where
      aux : (w' h' w h v : Rational) → w ≢ zero → v ≢ zero →
            w' ≡ v × (v ≡ zero → h' ≡ fromJustOrZero (div (mul h v) w)) ×
                     (v ≢ zero → div h' w' ≡ div (fromJustOrZero (div (mul h v) w)) v) →
            w' ≡ v × (w ≡ zero → h' ≡ h) × (w ≢ zero → div h' w' ≡ div h w)
      aux w' h' w h v w≢zero v≢zero (w'≡v , v≡zero→ , v≢zero→) with DivNonZero (mul h v) w w≢zero
      aux w' h' w h v w≢zero v≢zero (w'≡v , v≡zero→ , v≢zero→) | x , eq rewrite eq =
        w'≡v , (λ w≡zero → ⊥-elim (w≢zero w≡zero)) ,
        (λ _ → trans (v≢zero→ v≢zero) (CrossEq x v h w (DivMul (mul h v) w x eq) v≢zero w≢zero ))

  keepRatio-range : TripleR (λ { (_ , v) → v ≢ zero }) keepRatio (λ { (w' , _) → w' ≢ zero })
  keepRatio-range =
    conseq
      proj₁
      (case (•∷ᴬ (conseq
                    (λ { {(w , h) , v} (w≡v , w≢zero) →
                         subst (_≢ zero) w≡v w≢zero , trueFromWitness w≡v , falseFromWitness w≢zero , tt })
                    skip
                    (λ _ → tt) ,
                  (λ _ → refl , tt)) ∷ᴺ •∷ᴬ []))
      inj₁
