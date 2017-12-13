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
open import Data.Sum
open import Data.Bool
open import Data.Nat as Nat
open import Data.Nat.Properties
open import Data.List as List
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


OutOfRangeB : {n : ℕ} {F : Functor n} {S V : U n} → List (CaseBranch F S V) → ℙ (⟦ S ⟧ (μ F))
OutOfRangeB []                      = Π
OutOfRangeB ((_ , normal _ q) ∷ bs) = (False ∘ q) ∩ OutOfRangeB bs
OutOfRangeB ((_ , adaptive _) ∷ bs) = OutOfRangeB bs

mutual

  data Triple {n : ℕ} {F : Functor n} : {S V : U n} →
              ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F)) → BiGUL F S V → ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F)) → Set₁ where
    fail    : {S V : U n} → Triple ∅ (fail {S = S} {V}) ∅
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
              {b : BiGUL F T V} (R : ℙ (PatResult spat × ⟦ V ⟧ (μ F)))
                                (R' : ℙ (PatResult spat × PatResult spat × ⟦ V ⟧ (μ F))) →
              Triple ((Eval spat tpat expr ∘ swap) • R) b
                     (λ { (t' , t , v) → ∃ λ { (r' , r) → R' (r' , r , v) × Eval spat tpat expr (r' , t') ×
                                                                            Eval spat tpat expr (r , t) } }) →
              Triple (Match spat • R) (rearrS spat tpat expr c b)
                     (λ { (s' , s , v) → ∃ λ { (r' , r) → R' (r' , r , v) × Match spat (s' , r') × Match spat (s , r) } })
    rearrV  : {S V W : U n}
              {vpat : Pattern F V} {wpat : Pattern F W} {expr : Expr vpat wpat} {c : CompleteExpr vpat wpat expr}
              {b : BiGUL F S W} (R : ℙ (⟦ S ⟧ (μ F) × PatResult vpat)) (R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × PatResult vpat)) →
              Triple (R • Eval vpat wpat expr) b
                     (λ { (s' , s , v) → ∃ λ r → R' (s' , s , r) × Eval vpat wpat expr (r , v) }) →
              Triple (R • (Match vpat ∘ swap)) (rearrV vpat wpat expr c b)
                     (λ { (s' , s , v) → ∃ λ r → R' (s' , s , r) × Match vpat (v , r) })
    case    : {S V : U n} {bs : List (CaseBranch F S V)}
              {R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} {R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} →
              CaseBranchTriple R R'
                (NormalCaseDomain (List.map (Product.map id (elimCaseBranchType (λ _ _ → true) (λ _ → false))) bs)) bs [] →
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
                         (((True ∘ q) ∩ OutOfRangeB bs') ∘ proj₁)) →
            CaseBranchTriple R R' ReentryCond bs ((p , normal b q) ∷ bs') →
            CaseBranchTriple R R' ReentryCond ((p , normal b q) ∷ bs) bs'
    _∷ᴬ_ : {p : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Bool} {f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)}
           {bs bs' : List (CaseBranch F S V)} →
           ((s : ⟦ S ⟧ (μ F)) (v : ⟦ V ⟧ (μ F)) → (R ∩ (True ∘ uncurry p) ∩ OutOfDomain (List.map proj₁ bs')) (s , v) →
              (R ∩ ReentryCond) (f s v , v) × ((s' : ⟦ S ⟧ (μ F)) → R' (s' , f s v , v) → R' (s' , s , v))) →
           CaseBranchTriple R R' ReentryCond bs ((p , adaptive f) ∷ bs') →
           CaseBranchTriple R R' ReentryCond ((p , adaptive f) ∷ bs) bs'

infixr 5 _∷ᴺ_ _∷ᴬ_

case-main-cond-lemma : {n : ℕ} {F : Functor n} {S V : U n}
                       (bs : List (CaseBranch F S V)) → List.map proj₁ bs ≡ List.map proj₁ (interp-CaseBranch bs)
case-main-cond-lemma [] = refl
case-main-cond-lemma ((p , normal _ _) ∷ bs) = cong (p ∷_) (case-main-cond-lemma bs)
case-main-cond-lemma ((p , adaptive _) ∷ bs) = cong (p ∷_) (case-main-cond-lemma bs)

case-branch-type-lemma : {n : ℕ} {F : Functor n} {S V : U n} (bs : List (CaseBranch F S V)) →
                         List.map (Product.map id (elimCaseBranchType (λ _ _ → true) (λ _ → false))) bs ≡
                         List.map (Product.map id (isNormal _ _)) (interp-CaseBranch bs)
case-branch-type-lemma []                      = refl
case-branch-type-lemma ((p , normal _ _) ∷ bs) = cong ((p , true ) ∷_) (case-branch-type-lemma bs)
case-branch-type-lemma ((p , adaptive _) ∷ bs) = cong ((p , false) ∷_) (case-branch-type-lemma bs)

case-out-of-range-lemma : {n : ℕ} {F : Functor n} {S V : U n} (bs : List (CaseBranch F S V)) →
                          OutOfRangeB bs ⊆ OutOfRange (interp-CaseBranch bs)
case-out-of-range-lemma []                      = id
case-out-of-range-lemma ((p , normal _ _) ∷ bs) = Product.map id (case-out-of-range-lemma bs)
case-out-of-range-lemma ((p , adaptive _) ∷ bs) = case-out-of-range-lemma bs

case-out-of-range-inverse-lemma :
  {n : ℕ} {F : Functor n} {S V : U n} (bs : List (CaseBranch F S V)) →
  OutOfRange (interp-CaseBranch bs) ⊆ OutOfRangeB bs
case-out-of-range-inverse-lemma []                      = id
case-out-of-range-inverse-lemma ((p , normal _ _) ∷ bs) = Product.map id (case-out-of-range-inverse-lemma bs)
case-out-of-range-inverse-lemma ((p , adaptive _) ∷ bs) = case-out-of-range-inverse-lemma bs

soundness : {n : ℕ} {F : Functor n} {S V : U n}
            {R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} {b : BiGUL F S V} {R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} →
            Triple R b R' → Sound R (Lens.put (interp b)) R'
soundness fail = fail-soundness
soundness (skip {V = V} {f}) = skip-soundness (U-dec V) f
soundness replace = replace-soundness
soundness (prod {l = l} tl {r = r} tr) = prod-soundness _ _ (interp l) (soundness tl) _ _ (interp r) (soundness tr)
soundness (rearrS {tpat = tpat} {c = c} {b} R R' t) = rearrS-soundness _ tpat _ c (interp b) R R' (soundness t)
soundness (rearrV {wpat = wpat} {c = c} {b} R R' t) = rearrV-soundness _ wpat _ c (interp b) R R' (soundness t)
soundness {n} {F} {S} {V} (case {bs = bs} {R} {R'} ts dom) =
  case-soundness (interp-CaseBranch bs) R R'
    (subst (BranchSound R R' (interp-CaseBranch bs) [] ∘ NormalCaseDomain)
           (case-branch-type-lemma bs) (case-soundness-lemma ts))
    (subst (λ ps → R ⊆ CaseDomain ps) (case-main-cond-lemma bs) dom)
  where
    case-soundness-lemma : {bs bs' : List (CaseBranch F S V)} {ReentryCond : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} →
                           CaseBranchTriple R R' ReentryCond bs bs' →
                           BranchSound R R' (interp-CaseBranch bs) (interp-CaseBranch bs') ReentryCond
    case-soundness-lemma [] = tt
    case-soundness-lemma (t ∷ᴺ ts) with soundness t
    case-soundness-lemma {bs' = bs'} (t ∷ᴺ ts) | sound rewrite case-main-cond-lemma bs' =
      (λ sv pre → let (s' , put↦ , r' , (peq , outd) , qeq , outr) = sound sv pre
                  in   s' , put↦ , r' , (peq , outd) , qeq , case-out-of-range-lemma bs' outr) , case-soundness-lemma ts
    case-soundness-lemma {bs' = bs'} (p ∷ᴬ ts) rewrite case-main-cond-lemma bs' = lift p , case-soundness-lemma ts
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
expandTriple f measure R R' g zero   .zero z≤n     = g zero fail (conseq (λ { (_ , _ , ()) }) fail (λ { (() , _) }))
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

expand-sound :
  {n : ℕ} {F : Functor n} {S V : U n} (f : BiGUL F S V → BiGUL F S V)
  (measure : ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F) → ℕ) →
  (R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))) (R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))) →
  (l : ℕ) →((n : ℕ) → n ≤ l → Triple (R ∩ ((_≡ n) ∘ measure)) (expand (suc l) f) R') →
  Sound (R ∩ ((_≤ l) ∘ measure)) (Lens.put (interp (expand (suc l) f))) R'
expand-sound f measure R R' l ts (s , v) (Rsv , m≤l) = soundness (ts (measure (s , v)) m≤l) (s , v) (Rsv , refl)

mutual

  data TripleR {n : ℕ} {F : Functor n} : {S V : U n} →
               ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F)) → BiGUL F S V → ℙ (⟦ S ⟧ (μ F)) → Set₁ where
    fail    : {S V : U n} → TripleR ∅ (fail {S = S} {V}) ∅
    skip    : {S V : U n} {f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F)} →
              TripleR (uncurry _≡_ ∘ Product.map f id) (skip {S = S} {V} f) Π
    replace : {S : U n} → TripleR (uncurry _≡_) (replace {S = S}) Π
    prod    : {Sl Vl Sr Vr : U n}
              {Rl : ℙ (⟦ Sl ⟧ (μ F) × ⟦ Vl ⟧ (μ F))} {Pl : ℙ (⟦ Sl ⟧ (μ F))}
              {l : BiGUL F Sl Vl} → TripleR Rl l Pl →
              {Rr : ℙ (⟦ Sr ⟧ (μ F) × ⟦ Vr ⟧ (μ F))} {Pr : ℙ (⟦ Sr ⟧ (μ F))}
              {r : BiGUL F Sr Vr} → TripleR Rr r Pr →
              TripleR (λ { ((sl , sr) , (vl , vr)) → Rl (sl , vl) × Rr (sr , vr) })
                      (prod l r)
                      (λ { (sl , sr) → Pl sl × Pr sr })
    rearrS  : {S T V : U n}
              {spat : Pattern F S} {tpat : Pattern F T} {expr : Expr spat tpat} {c : CompleteExpr spat tpat expr}
              {b : BiGUL F T V} (R : ℙ (PatResult spat × ⟦ V ⟧ (μ F))) (P : ℙ (PatResult spat)) →
              TripleR ((Eval spat tpat expr ∘ swap) • R) b (λ t → ∃ λ r → P r × Eval spat tpat expr (r , t)) →
              TripleR (Match spat • R) (rearrS spat tpat expr c b) (λ s → ∃ λ r → P r × Match spat (s , r))
    rearrV  : {S V W : U n}
              {vpat : Pattern F V} {wpat : Pattern F W} {expr : Expr vpat wpat} {c : CompleteExpr vpat wpat expr}
              {b : BiGUL F S W} (R : ℙ (⟦ S ⟧ (μ F) × PatResult vpat)) {P : ℙ (⟦ S ⟧ (μ F))} →
              TripleR (R • Eval vpat wpat expr) b P →
              TripleR (R • (Match vpat ∘ swap)) (rearrV vpat wpat expr c b) P
    case    : {S V : U n} {bs : List (CaseBranch F S V)} {R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} →
              (ts : CaseBranchTripleR R bs []) → TripleR R (case bs) (CaseRange ts)
    conseq  : {S V : U n} {b : BiGUL F S V} {R T : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} {P Q : ℙ (⟦ S ⟧ (μ F))} →
              R ∩ (Q ∘ proj₁) ⊆ T → TripleR R b P → Q ⊆ P → TripleR T b Q

  data CaseBranchTripleR {n : ℕ} {F : Functor n} {S V : U n} (R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))) :
                         List (CaseBranch F S V) → List (CaseBranch F S V) → Set₁ where
    []   : {bs' : List (CaseBranch F S V)} → CaseBranchTripleR R [] bs'
    _∷ᴺ_ : {p : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Bool} {b : BiGUL F S V} {q : ⟦ S ⟧ (μ F) → Bool}
           {bs bs' : List (CaseBranch F S V)} {P : ℙ (⟦ S ⟧ (μ F))} →
           TripleR (R ∩ (True ∘ uncurry p) ∩ OutOfDomain (List.map proj₁ bs')) b P →
           CaseBranchTripleR R bs ((p , normal b q) ∷ bs') → CaseBranchTripleR R ((p , normal b q) ∷ bs) bs'
    •∷ᴬ_ : {p : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Bool} {f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)}
           {bs bs' : List (CaseBranch F S V)} →
           CaseBranchTripleR R bs ((p , adaptive f) ∷ bs') → CaseBranchTripleR R ((p , adaptive f) ∷ bs) bs'

  CaseRange : {n : ℕ} {F : Functor n} {S V : U n} {R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))}
              {bs bs' : List (CaseBranch F S V)} → CaseBranchTripleR R bs bs' → ℙ (⟦ S ⟧ (μ F))
  CaseRange             []                          = ∅
  CaseRange {bs' = bs'} (_∷ᴺ_ {q = q} {P = P} _ ts) = (P ∩ (True ∘ q) ∩ OutOfRangeB bs') ∪ CaseRange ts
  CaseRange             (•∷ᴬ                    ts) = CaseRange ts

infixr 5 •∷ᴬ_

soundnessR : {n : ℕ} {F : Functor n} {S V : U n}
             {R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} {b : BiGUL F S V} {P : ℙ (⟦ S ⟧ (μ F))} →
             TripleR R b P → SoundG P (Lens.get (interp b)) R
soundnessR fail = fail-soundnessG
soundnessR (skip {V = V} {f}) = skip-soundnessG (U-dec V) f
soundnessR replace = replace-soundnessG
soundnessR (prod {l = l} tl {r = r} tr) = prod-soundnessG _ _ (interp l) (soundnessR tl) _ _ (interp r) (soundnessR tr)
soundnessR (rearrS {tpat = tpat} {c = c} {b} R P t) = rearrS-soundnessG _ tpat _ c (interp b) P R (soundnessR t) 
soundnessR (rearrV {wpat = wpat} {c = c} {b} R   t) = rearrV-soundnessG _ wpat _ c (interp b) _ R (soundnessR t)
soundnessR {n} {F} {S} {V} {R} (case {bs = bs} ts) =
  case-soundnessG (interp-CaseBranch bs) R (case-soundnessR-lemma ts) (CaseRange ts) (case-range-lemma ts)
  where
    case-soundnessR-lemma :
      {bs bs' : List (CaseBranch F S V)} → CaseBranchTripleR R bs bs' →
      BranchSoundG R (interp-CaseBranch bs) (interp-CaseBranch bs')
    case-soundnessR-lemma [] = tt
    case-soundnessR-lemma {bs' = bs'} (_∷ᴺ_ {P = P} t ts)
      rewrite case-main-cond-lemma bs' = (P , soundnessR t) , case-soundnessR-lemma ts
    case-soundnessR-lemma (•∷ᴬ ts) = case-soundnessR-lemma ts

    case-range-lemma :
      {bs bs' : List (CaseBranch F S V)} (ts : CaseBranchTripleR R bs bs') →
      CaseRange ts ⊆ Range R (interp-CaseBranch bs) (interp-CaseBranch bs') (case-soundnessR-lemma ts)
    case-range-lemma [] ()
    case-range-lemma {bs' = bs'} (_ ∷ᴺ ts) (inj₁ (p , q , out))
      rewrite case-main-cond-lemma bs' = inj₁ (p , q , case-out-of-range-lemma bs' out)
    case-range-lemma {bs' = bs'} (_ ∷ᴺ ts) (inj₂ r) rewrite case-main-cond-lemma bs' = inj₂ (case-range-lemma ts r)
    case-range-lemma (•∷ᴬ ts) r = case-range-lemma ts r
soundnessR (conseq R∩Q⊆T t Q⊆P) = consequenceG _ _ _ (soundnessR t) _ Q⊆P _ R∩Q⊆T

expandTripleR :
  {n : ℕ} {F : Functor n} {S V : U n} (f : BiGUL F S V → BiGUL F S V)
  (measure : ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F) → ℕ) →
  (R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))) (P : ℕ → ℙ (⟦ S ⟧ (μ F))) →
  ((n : ℕ) (rec : BiGUL F S V) → ({m : ℕ} → TripleR (R ∩ ((_≡ m) ∘ measure)) rec (P m ∩ (λ _ → m < n))) →
                                 TripleR (R ∩ ((_≡ n) ∘ measure)) (f rec) (P n)) →
  (l n : ℕ) → n ≤ l → TripleR (R ∩ ((_≡ n) ∘ measure)) (expand (suc l) f) (P n) 
expandTripleR f measure R P g zero   .zero z≤n     = g zero fail (conseq (λ { (() , _) }) fail (λ { (_ , ()) }))
expandTripleR f measure R P g (suc l) n    n≤suc-l = g n (expand (suc l) f) aux
  where
    aux : {m : ℕ} → TripleR (R ∩ ((_≡ m) ∘ measure)) (expand (suc l) f) (P m ∩ (λ _ → m < n))
    aux {m} with suc m ≤? n
    aux {m} | yes m<n = conseq proj₁
                               (expandTripleR f measure R P g l m
                                  (≤-pred (DecTotalOrder.trans Nat.decTotalOrder m<n n≤suc-l)))
                               proj₁
    aux {m} | no ¬m<n = conseq (λ { (_ , _ , m<n) → ⊥-elim (¬m<n m<n) })
                               (expandTripleR f measure R P g l l (DecTotalOrder.refl Nat.decTotalOrder))
                               (λ { (_ , m<n) → ⊥-elim (¬m<n m<n) })

expand-soundG :
  {n : ℕ} {F : Functor n} {S V : U n} (f : BiGUL F S V → BiGUL F S V)
  (measure : ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F) → ℕ)
  (R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))) (P' : ℕ → ℙ (⟦ S ⟧ (μ F)))
  (l : ℕ) → ((n : ℕ) → n ≤ l → TripleR (R ∩ ((_≡ n) ∘ measure)) (expand (suc l) f) (P' n)) →
  SoundG (λ s → Σ[ n ∈ ℕ ] n ≤ l × P' n s) (Lens.get (interp (expand (suc l) f))) (R ∩ ((_≤ l) ∘ measure))
expand-soundG f measure R P' l ts s (n , n≤l , P'-n-s) =
  let (v , get↦ , Rsv , meq) = soundnessR (ts n n≤l) s P'-n-s
  in  v , get↦ , Rsv , subst (_≤ l) (sym meq) n≤l
