module HoareLogic.Case {S V : Set} where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens
open import DynamicallyChecked.Case S V
open import HoareLogic.Semantics

open import Level
open import Function
open import Data.Bool
open import Data.Product as Product
open import Data.Sum
open import Data.List as List
open import Relation.Binary.PropositionalEquality


DecCaseDomain : List (S → V → Bool) → ℙ (S × V)
DecCaseDomain []       = ∅
DecCaseDomain (c ∷ cs) = (True ∘ uncurry c) ∪ ((False ∘ uncurry c) ∩ DecCaseDomain cs)

CaseDomain : List (S → V → Bool) → ℙ (S × V)
CaseDomain []       = ∅
CaseDomain (c ∷ cs) = (True ∘ uncurry c) ∪ CaseDomain cs

toDecCaseDomain : (cs : List (S → V → Bool)) → CaseDomain cs ⊆ DecCaseDomain cs
toDecCaseDomain []               ()
toDecCaseDomain (c ∷ cs)         (inj₁ c-true) = inj₁ c-true
toDecCaseDomain (c ∷ cs) {s , v} (inj₂ cs-dom) with c s v
toDecCaseDomain (c ∷ cs)         (inj₂ cs-dom) | true  = inj₁ refl
toDecCaseDomain (c ∷ cs)         (inj₂ cs-dom) | false = inj₂ (refl , toDecCaseDomain cs cs-dom)

NormalDecCaseDomain : List ((S → V → Bool) × Bool) → ℙ (S × V)
NormalDecCaseDomain []                 = ∅
NormalDecCaseDomain ((c , true ) ∷ bs) = (True ∘ uncurry c) ∪ ((False ∘ uncurry c) ∩ NormalDecCaseDomain bs)
NormalDecCaseDomain ((c , false) ∷ bs) = (False ∘ uncurry c) ∩ NormalDecCaseDomain bs

NormalCaseDomain : List ((S → V → Bool) × Bool) → ℙ (S × V)
NormalCaseDomain []                 = ∅
NormalCaseDomain ((c , true ) ∷ bs) = (True ∘ uncurry c) ∪ NormalCaseDomain bs
NormalCaseDomain ((c , false) ∷ bs) = (False ∘ uncurry c) ∩ NormalCaseDomain bs

toNormalDecCaseDomain : (bs : List ((S → V → Bool) × Bool)) → NormalCaseDomain bs ⊆ NormalDecCaseDomain bs
toNormalDecCaseDomain []                         ()
toNormalDecCaseDomain ((c , true ) ∷ bs)         (inj₁ c-true) = inj₁ c-true
toNormalDecCaseDomain ((c , true ) ∷ bs) {s , v} (inj₂ bs-dom) with c s v
toNormalDecCaseDomain ((c , true ) ∷ bs)         (inj₂ bs-dom) | true  = inj₁ refl
toNormalDecCaseDomain ((c , true ) ∷ bs)         (inj₂ bs-dom) | false = inj₂ (refl , toNormalDecCaseDomain bs bs-dom)
toNormalDecCaseDomain ((c , false) ∷ bs)         (c-false , bs-dom) = c-false , toNormalDecCaseDomain bs bs-dom

OutOfDomain : List (S → V → Bool) → ℙ (S × V)
OutOfDomain []       = Π
OutOfDomain (p ∷ ps) = (False ∘ uncurry p) ∩ OutOfDomain ps

invertRange : BranchType → ℙ S
invertRange = elimBranchType (λ _ q → False ∘ q) (λ _ → Π)

OutOfRange : List Branch → ℙ S
OutOfRange = foldr (_∩_ ∘ invertRange ∘ proj₂) Π

RangeDisjoint : List Branch → List Branch → Set
RangeDisjoint []             bs' = ⊤
RangeDisjoint ((p , normal l q) ∷ bs) bs' = ((True ∘ q) ⊆ OutOfRange bs') × RangeDisjoint bs ((p , normal l q) ∷ bs')
RangeDisjoint ((p , adaptive f) ∷ bs) bs' = RangeDisjoint bs ((p , adaptive f) ∷ bs')

BranchSound : (R : ℙ (S × V)) (R' : ℙ (S × S × V)) → List Branch → List Branch → ℙ (S × V) → Set₁
BranchSound R R' []             bs' ReentryCond = ⊤
BranchSound R R' ((p , b) ∷ bs) bs' ReentryCond =
  let Pre = R ∩ (True ∘ uncurry p) ∩ OutOfDomain (List.map proj₁ bs')
  in  elimBranchType
        (λ l q → Sound Pre (Lens.put l)
                       (R' ∩ (((True ∘ uncurry p) ∩ OutOfDomain (List.map proj₁ bs')) ∘ Product.map id proj₂) ∩
                             (True ∘ q ∘ proj₁)))
        (λ f → Lift ((Pre ⊆ (R ∩ ReentryCond) ∘ < uncurry f , proj₂ >) × 
                     ((Pre ∘ proj₂) ∩ (R' ∘ Product.map id < uncurry f , proj₂ >) ⊆ R'))) b ×
  BranchSound R R' bs ((p , b) ∷ bs') ReentryCond

check-diversion-success : (bs : List Branch) (s : S) (v : V) →
                          OutOfDomain (List.map proj₁ bs) (s , v) → OutOfRange bs s → check-diversion bs s v ↦ tt
check-diversion-success []                      s v                outd               outr  = return refl
check-diversion-success ((p , normal l q) ∷ bs) s v (p-s-v≡false , outd) (q-s≡false , outr) =
  assert-not p-s-v≡false then catch-snd (assert-fst q-s≡false) (check-diversion-success bs s v outd outr)
check-diversion-success ((p , adaptive f) ∷ bs) s v (p-s-v≡false , outd) (q-s≡false , outr) =
  assert-not p-s-v≡false then catch-snd fail (check-diversion-success bs s v outd outr)

case-soundness-reentry :
  (bs bs' : List Branch) (R : ℙ (S × V)) (R' : ℙ (S × S × V)) (cont : S → Par S) (ReentryCond : ℙ (S × V)) →
  BranchSound R R' bs bs' ReentryCond → RangeDisjoint bs bs' →
  (s : S) (v : V) → R (s , v) → NormalDecCaseDomain (List.map (Product.map id isNormal) bs) (s , v) → OutOfDomain (List.map proj₁ bs') (s , v) →
  Σ[ s' ∈ S ] ((put-with-adaptation bs bs' s v cont ↦ s') × R' (s' , s , v))
case-soundness-reentry []                      bs' R R' cont ReentryCond sound disj s v sRv ()  out
case-soundness-reentry ((p , normal l q) ∷ bs) bs' R R' cont ReentryCond (b-sound , sound) (b-disj , disj) s v sRv (inj₁ p-s-v≡true) out
  rewrite p-s-v≡true =
  let (s' , l-s-v↦s' , s'R'v , (p-s'-v≡true , outd-s'-v) , q-s'≡true) = b-sound (s , v) (sRv , p-s-v≡true , out)
  in  s' , (l-s-v↦s' >>= assert p-s'-v≡true then assert q-s'≡true then
            check-diversion-success bs' s' v outd-s'-v (b-disj q-s'≡true) >>= return refl) , s'R'v
case-soundness-reentry ((p , normal l q) ∷ bs) bs' R R' cont ReentryCond (_ , sound) (b-disj , disj) s v sRv (inj₂ (p-s-v≡false , dom)) out
  rewrite p-s-v≡false =
  case-soundness-reentry bs ((p , normal l q) ∷ bs') R R' cont ReentryCond sound disj s v sRv dom (p-s-v≡false , out)
case-soundness-reentry ((p , adaptive f) ∷ bs) bs' R R' cont ReentryCond (_ , sound) disj s v sRv (p-s-v≡false , dom) out
  rewrite p-s-v≡false =
  case-soundness-reentry bs ((p , adaptive f) ∷ bs') R R' cont ReentryCond sound disj s v sRv dom (p-s-v≡false , out)

case-soundness-main :
  (bs bs' : List Branch) (R : ℙ (S × V)) (R' : ℙ (S × S × V)) (cont : S → Par S) (ReentryCond : ℙ (S × V)) →
  BranchSound R R' bs bs' ReentryCond → RangeDisjoint bs bs' →
  (s : S) (v : V) → R (s , v) → DecCaseDomain (List.map proj₁ bs) (s , v) → OutOfDomain (List.map proj₁ bs') (s , v) →
  ((s'' : S) → R (s'' , v) → ReentryCond (s'' , v) → Σ[ s' ∈ S ] ((cont s'' ↦ s') × R' (s' , s'' , v))) →
  Σ[ s' ∈ S ] ((put-with-adaptation bs bs' s v cont ↦ s') × R' (s' , s , v))
case-soundness-main []             bs' R R' cont ReentryCond sound disj s v sRv ()  out cont-sound
case-soundness-main ((p , normal l q) ∷ bs) bs' R R' cont ReentryCond (b-sound , sound) (b-disj , disj) s v sRv (inj₁ p-s-v≡true) out cont-sound
  rewrite p-s-v≡true =
  let (s' , l-s-v↦s' , s'R'v , (p-s'-v≡true , outd-s'-v) , q-s'≡true) = b-sound (s , v) (sRv , p-s-v≡true , out)
  in  s' , (l-s-v↦s' >>= assert p-s'-v≡true then assert q-s'≡true then
            check-diversion-success bs' s' v outd-s'-v (b-disj q-s'≡true) >>= return refl) , s'R'v
case-soundness-main ((p , adaptive f) ∷ bs) bs' R R' cont ReentryCond (lift (b-reentry , b-sound) , sound) disj s v sRv (inj₁ p-s-v≡true) out cont-sound
  rewrite p-s-v≡true = let (f-s-v-R-v , reentry) = b-reentry (sRv , p-s-v≡true , out)
                           (s' , cont↦ , R'-s') = cont-sound (f s v) f-s-v-R-v reentry
                       in  s' , cont↦ , b-sound ((sRv , p-s-v≡true , out) , R'-s')
case-soundness-main ((p , normal l q) ∷ bs) bs' R R' cont ReentryCond (_ , sound) (b-disj , disj) s v sRv (inj₂ (p-s-v≡false , dom)) out cont-sound
  rewrite p-s-v≡false =
  case-soundness-main bs ((p , normal l q) ∷ bs') R R' cont ReentryCond sound disj s v sRv dom (p-s-v≡false , out) cont-sound
case-soundness-main ((p , adaptive f) ∷ bs) bs' R R' cont ReentryCond (_ , sound) disj s v sRv (inj₂ (p-s-v≡false , dom)) out cont-sound
  rewrite p-s-v≡false =
  case-soundness-main bs ((p , adaptive f) ∷ bs') R R' cont ReentryCond sound disj s v sRv dom (p-s-v≡false , out) cont-sound

case-soundness : (bs : List Branch) (R : ℙ (S × V)) (R' : ℙ (S × S × V)) →
                 BranchSound R R' bs [] (NormalCaseDomain (List.map (Product.map id isNormal) bs)) →
                 R ⊆ CaseDomain (List.map proj₁ bs) →
                 RangeDisjoint bs [] →
                 Sound R (Lens.put (case-lens bs)) R'
case-soundness bs R R' sound dom disj (s , v) sRv =
  case-soundness-main bs [] R R'
    (λ s' → put-with-adaptation bs [] s' v (const fail)) (NormalCaseDomain (List.map (Product.map id isNormal) bs)) sound disj s v sRv (toDecCaseDomain (List.map proj₁ bs) (dom sRv)) tt
    (λ s' s'Rv dom' → case-soundness-reentry bs [] R R' (const fail) (NormalCaseDomain (List.map (Product.map id isNormal) bs)) sound disj s' v s'Rv (toNormalDecCaseDomain (List.map (Product.map id isNormal) bs) dom') tt)
