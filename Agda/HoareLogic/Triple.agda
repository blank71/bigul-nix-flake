module HoareLogic.Triple where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Lens
open import DynamicallyChecked.Universe
open import DynamicallyChecked.Case
open import DynamicallyChecked.BiGUL
open import DynamicallyChecked.Rearrangement
open import HoareLogic.Semantics
open import HoareLogic.Rearrangement
open import HoareLogic.Case

open import Level using (lift)
open import Function
open import Data.Empty
open import Data.Product as Product
open import Data.Bool
open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.List as List
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


mutual

  data Triple {n : ℕ} {F : Functor n} : {S V : U n} →
              ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F)) → BiGUL F S V → ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F)) → Set₁ where
    fail    : {S V : U n} {R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} → Triple ∅ (fail {S = S} {V}) R'
    skip    : {S V : U n} {f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F)} →
              Triple (uncurry _≡_ ∘ Product.map f id) (skip {S = S} {V} f) (uncurry _≡_ ∘ Product.map id proj₁)
    replace : {S : U n} → Triple Π (replace {S = S}) (uncurry _≡_ ∘ Product.map id proj₂)
    prod    : {Sl Vl Sr Vr : U n}
              {Rl : ℙ (⟦ Sl ⟧ (μ F) × ⟦ Vl ⟧ (μ F))} {Rl' : ℙ (⟦ Sl ⟧ (μ F) × ⟦ Sl ⟧ (μ F) × ⟦ Vl ⟧ (μ F))}
              {l : BiGUL F Sl Vl} → Triple Rl l Rl' →
              {Rr : ℙ (⟦ Sr ⟧ (μ F) × ⟦ Vr ⟧ (μ F))} {Rr' : ℙ (⟦ Sr ⟧ (μ F) × ⟦ Sr ⟧ (μ F) × ⟦ Vr ⟧ (μ F))}
              {r : BiGUL F Sr Vr} → Triple Rr r Rr' →
              Triple (λ { ((sl , sr) , (vl , vr)) → Rl (sl , vl) × Rr (sr , vr) }) (prod l r)
                     (λ { ((sl' , sr') , (sl , sr) , (vl , vr)) → Rl' (sl' , sl , vl) × Rr' (sr' , sr , vr) })
    rearrS  : {S T V : U n}
              {spat : Pattern F S} {tpat : Pattern F T} {expr : Expr spat tpat} {c : CompleteExpr spat tpat expr}
              {b : BiGUL F T V} (R : ℙ (PatResult spat × ⟦ V ⟧ (μ F))) (R' : ℙ (PatResult spat × PatResult spat × ⟦ V ⟧ (μ F))) →
              Triple ((Eval spat tpat expr ∘ swap) • R) b
                     (λ { (t' , t , v) → ∃ λ { (r' , r) → R' (r' , r , v) × Eval spat tpat expr (r' , t') × Eval spat tpat expr (r , t) } }) →
              Triple (Match spat • R) (rearrS spat tpat expr c b)
                     (λ { (s' , s , v) → ∃ λ { (r' , r) → R' (r' , r , v) × Match spat (s' , r') × Match spat (s , r) } })
    rearrV  : {S V W : U n}
              {vpat : Pattern F V} {wpat : Pattern F W} {expr : Expr vpat wpat} {c : CompleteExpr vpat wpat expr}
              {b : BiGUL F S W} (R : ℙ (⟦ S ⟧ (μ F) × PatResult vpat)) (R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × PatResult vpat)) →
              Triple (R • Eval vpat wpat expr) b
                     (λ { (s' , s , v) → ∃ λ r → R' (s' , s , r) × Eval vpat wpat expr (r , v) }) →
              Triple (R • (Match vpat ∘ swap)) (rearrV vpat wpat expr c b)
                     (λ { (s' , s , v) → ∃ λ r → R' (s' , s , r) × Match vpat (v , r) })
    dep     : {S V V' : U n} {f : ⟦ V ⟧ (μ F) → ⟦ V' ⟧ (μ F)} {b : BiGUL F S V}
              (R : ℙ (⟦ S ⟧ (μ F) × (⟦ V ⟧ (μ F) × ⟦ V' ⟧ (μ F)))) {R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × (⟦ V ⟧ (μ F) × ⟦ V' ⟧ (μ F)))} →
              Triple (R ∘ Product.map id < id , f >) b (R' ∘ Product.map id (Product.map id < id , f >)) →
              Triple ((uncurry _≡_ ∘ Product.map f id ∘ proj₂) ∩ R) (dep {S = S} {V} {V'} f b) R'
    case    : {S V : U n} {bs : List (CaseBranch F S V)}
              {R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} {R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} →
              CaseBranchTriple R R'
                ((NormalCaseDomain (List.map (Product.map id (elimCaseBranchType (λ _ _ → true) (λ _ → false))) bs))) bs [] →
              R ⊆ CaseDomain (List.map proj₁ bs) →
              Triple R (case bs) R'
    conseq  : {S V : U n} {b : BiGUL F S V}
              {R Q : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} {R' Q' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} →
              Q ⊆ R → Triple R b R' → R' ∩ (Q ∘ proj₂) ⊆ Q' → Triple Q b Q'

  data CaseBranchTriple {n : ℕ} {F : Functor n} {S V : U n}
                        (R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))) (R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F)))
                        (ReentryCond : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))) :
                        List (CaseBranch F S V) → List (CaseBranch F S V) → Set₁ where
    []    : {bs' : List (CaseBranch F S V)} → CaseBranchTriple R R' ReentryCond [] bs'
    _∷ᴺ_  : {p : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Bool} {b : BiGUL F S V} {q : ⟦ S ⟧ (μ F) → Bool}
            {bs bs' : List (CaseBranch F S V)} →
            Triple (R ∩ (True ∘ uncurry p) ∩ OutOfDomain (List.map proj₁ bs')) b
                   (R' ∩ (((True ∘ uncurry p) ∩ OutOfDomain (List.map proj₁ bs')) ∘ Product.map id proj₂) ∩
                         (True ∘ q ∘ proj₁)) ×
            ((True ∘ q) ⊆ foldr (_∩_ ∘ elimCaseBranchType (λ _ q → False ∘ q) (λ _ → Π)∘ proj₂) Π bs') →
            CaseBranchTriple R R' ReentryCond bs ((p , normal b q) ∷ bs') →
            CaseBranchTriple R R' ReentryCond ((p , normal b q) ∷ bs) bs'
    _∷ᴬ_ : {p : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Bool} {f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)}
           {bs bs' : List (CaseBranch F S V)} →
           let Pre = R ∩ (True ∘ uncurry p) ∩ OutOfDomain (List.map proj₁ bs')
           in  ((Pre ⊆ (R ∩ ReentryCond) ∘ < uncurry f , proj₂ >) × 
                ((Pre ∘ proj₂) ∩ (R' ∘ Product.map id < uncurry f , proj₂ >) ⊆ R')) →
               CaseBranchTriple R R' ReentryCond bs ((p , adaptive f) ∷ bs') →
               CaseBranchTriple R R' ReentryCond ((p , adaptive f) ∷ bs) bs'

infixr 5 _∷ᴺ_ _∷ᴬ_

soundness : {n : ℕ} {F : Functor n} {S V : U n}
            {R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} {b : BiGUL F S V} {R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} →
            Triple R b R' → Sound R (Lens.put (interp b)) R'
soundness fail = fail-soundness _
soundness {V = V} (skip {f = f}) = skip-soundness (U-dec V) f
soundness replace = replace-soundness
soundness (prod {l = l} tl {r = r} tr) = prod-soundness _ _ (interp l) (soundness tl) _ _ (interp r) (soundness tr)
soundness (rearrS {tpat = tpat} {c = c} {b} R R' t) = rearrS-soundness _ tpat _ c (interp b) R R' (soundness t)
soundness (rearrV {wpat = wpat} {c = c} {b} R R' t) = rearrV-soundness _ wpat _ c (interp b) R R' (soundness t)
soundness (dep {V' = V'} {f} {b} R {R'} t) = dep-soundness f (U-dec V') (interp b) R R' (soundness t)
soundness {n} {F} {S} {V} (case {bs = bs} {R} {R'} ts dom) =
  case-soundness (interp-CaseBranch bs) R R'
    (subst (BranchSound R R' (interp-CaseBranch bs) [] ∘ NormalCaseDomain)
           (case-branch-type-lemma bs) (case-soundness-lemma ts))
    (subst (λ ps → R ⊆ CaseDomain ps) (case-main-cond-lemma bs) dom)
    (case-disjointness-lemma ts)
  where
    case-main-cond-lemma : (bs : List (CaseBranch F S V)) → List.map proj₁ bs ≡ List.map proj₁ (interp-CaseBranch bs)
    case-main-cond-lemma [] = refl
    case-main-cond-lemma ((p , normal _ _) ∷ bs) = cong (p ∷_) (case-main-cond-lemma bs)
    case-main-cond-lemma ((p , adaptive _) ∷ bs) = cong (p ∷_) (case-main-cond-lemma bs)
    
    case-soundness-lemma : {bs bs' : List (CaseBranch F S V)} {ReentryCond : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} →
                           CaseBranchTriple R R' ReentryCond bs bs' →
                           BranchSound R R' (interp-CaseBranch bs) (interp-CaseBranch bs') ReentryCond
    case-soundness-lemma [] = tt
    case-soundness-lemma ((t , _) ∷ᴺ ts) with soundness t
    case-soundness-lemma {bs' = bs'} ((t , _) ∷ᴺ ts) | s rewrite case-main-cond-lemma bs' = s , case-soundness-lemma ts
    case-soundness-lemma {bs' = bs'} (r ∷ᴬ ts) rewrite case-main-cond-lemma bs' = lift r , case-soundness-lemma ts

    case-branch-type-lemma : (bs : List (CaseBranch F S V)) →
                             List.map (Product.map id (elimCaseBranchType (λ _ _ → true) (λ _ → false))) bs ≡
                             List.map (Product.map id (isNormal _ _)) (interp-CaseBranch bs)
    case-branch-type-lemma [] = refl
    case-branch-type-lemma ((p , normal _ _) ∷ bs) = cong ((p , true ) ∷_) (case-branch-type-lemma bs)
    case-branch-type-lemma ((p , adaptive _) ∷ bs) = cong ((p , false) ∷_) (case-branch-type-lemma bs)

    case-out-of-range-lemma : (bs : List (CaseBranch F S V)) →
                              foldr (_∩_ ∘ elimCaseBranchType (λ _ q → False ∘ q) (λ _ → Π)∘ proj₂) Π bs ⊆
                              OutOfRange (interp-CaseBranch bs)
    case-out-of-range-lemma [] = id
    case-out-of-range-lemma ((p , normal _ _) ∷ bs) = Product.map id (case-out-of-range-lemma bs)
    case-out-of-range-lemma ((p , adaptive _) ∷ bs) = Product.map (const tt) (case-out-of-range-lemma bs)

    case-disjointness-lemma : {bs bs' : List (CaseBranch F S V)} {ReentryCond : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} →
                              CaseBranchTriple R R' ReentryCond bs bs' →
                              RangeDisjoint (interp-CaseBranch bs) (interp-CaseBranch bs')
    case-disjointness-lemma [] = tt
    case-disjointness-lemma {bs' = bs'} ((t , x) ∷ᴺ ts) = case-out-of-range-lemma bs' ∘ x , case-disjointness-lemma ts
    case-disjointness-lemma (_ ∷ᴬ ts) = case-disjointness-lemma ts
soundness (conseq q t q') = consequence _ _ _ (soundness t) _ q _ q'

expand : ℕ → {n : ℕ} {F : Functor n} {S V : U n} → (BiGUL F S V → BiGUL F S V) → BiGUL F S V
expand zero    f = fail
expand (suc n) f = f (expand n f)

expandTriple :
  {n : ℕ} {F : Functor n} {S V : U n} (f : BiGUL F S V → BiGUL F S V)
  (measure : ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F) → ℕ) →
  (R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))) (R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))) →
  ((n : ℕ) (rec : BiGUL F S V) → ({m : ℕ} → Triple (R ∩ ((_≡ m) ∘ measure) ∩ (λ _ → m < n)) rec R') →
                                 Triple (R ∩ ((_≡ n) ∘ measure)) (f rec) R') →
  (l n : ℕ) → n ≤ l → Triple (R ∩ ((_≡ n) ∘ measure)) (expand (suc l) f) R'
expandTriple f measure R R' g zero   .zero z≤n     = g zero fail (conseq (λ { (_ , _ , ()) }) fail proj₁)
expandTriple f measure R R' g (suc l) n    n≤suc-l = g n (expand (suc l) f) aux
  where
    aux : {m : ℕ} → Triple (R ∩ ((_≡ m) ∘ measure) ∩ (λ _ → m < n)) (expand (suc l) f) R'
    aux {m} with suc m ≤? n
    aux {m} | yes m<n = conseq (Product.map id proj₁)
                               (expandTriple f measure R R' g l m
                                  (≤-pred (DecTotalOrder.trans Nat.decTotalOrder m<n n≤suc-l)))
                               proj₁
    aux {m} | no ¬m<n = conseq (λ { (_ , _ , m<n) → ⊥-elim (¬m<n m<n) })
                               (expandTriple f measure R R' g l l (DecTotalOrder.refl Nat.decTotalOrder))
                               proj₁
