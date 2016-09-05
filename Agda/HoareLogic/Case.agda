module HoareLogic.Case (S V : Set) where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens
open import DynamicallyChecked.Case S V
open import HoareLogic.Triple

open import Level
open import Function
open import Data.Bool
open import Data.Product as Product
open import Data.Sum
open import Data.List
open import Relation.Binary.PropositionalEquality


CaseDomain : List Branch → ℙ (S × V)
CaseDomain []             _       = ⊥
CaseDomain ((p , _) ∷ bs) (s , v) = (p s v ≡ true) ⊎ ((p s v ≡ false) × CaseDomain bs (s , v))

NormalCaseDomain : List Branch → ℙ (S × V)
NormalCaseDomain []                      _       = ⊥
NormalCaseDomain ((p , normal l q) ∷ bs) (s , v) = (p s v ≡ true) ⊎ ((p s v ≡ false) × NormalCaseDomain bs (s , v))
NormalCaseDomain ((p , adaptive f) ∷ bs) (s , v) = (p s v ≡ false) × NormalCaseDomain bs (s , v)

OutOfDomain : List Branch → ℙ (S × V)
OutOfDomain []             _       = ⊤
OutOfDomain ((p , b) ∷ bs) (s , v) = p s v ≡ false × OutOfDomain bs (s , v)

OutOfRange : List Branch → ℙ S
OutOfRange []             s = ⊤
OutOfRange ((p , b) ∷ bs) s = elimBranchType (λ l q → q s ≡ false) (λ f → ⊤) b × OutOfRange bs s

RangeDisjoint : List Branch → List Branch → Set
RangeDisjoint []             bs' = ⊤
RangeDisjoint ((p , b) ∷ bs) bs' = elimBranchType (λ l q → (s : S) → q s ≡ true → OutOfRange bs' s) (λ f → ⊤) b ×
                                   RangeDisjoint bs ((p , b) ∷ bs')

BranchSound : (R : ℙ (S × V)) (R' : ℙ (S × S × V)) → List Branch → List Branch → ℙ (S × V) → Set₁
BranchSound R R' []             bs' ReentryCond = ⊤
BranchSound R R' ((p , b) ∷ bs) bs' ReentryCond =
  elimBranchType
    (λ l q → Sound (R ∩ boolℙ (uncurry p) ∩ OutOfDomain bs')
                   (Lens.put l)
                   (R' ∩ inv (Product.map id proj₂) (boolℙ (uncurry p) ∩ OutOfDomain bs') ∩ inv proj₁ (boolℙ q)))
    (λ f → Lift ((s : S) (v : V) → R (s , v) → p s v ≡ true →
                   R (f s v , v) × ReentryCond (f s v , v) × ((s' : S) → R' (s' , f s v , v) → R' (s' , s , v)))) b ×
  BranchSound R R' bs ((p , b) ∷ bs') ReentryCond

check-diversion-success :
  (bs : List Branch) (s : S) (v : V) → OutOfDomain bs (s , v) → OutOfRange bs s → check-diversion bs s v ↦ tt
check-diversion-success []                      s v                outd               outr  = return refl
check-diversion-success ((p , normal l q) ∷ bs) s v (p-s-v≡false , outd) (q-s≡false , outr) =
  assert-not p-s-v≡false then catch-snd (assert-fst q-s≡false) (check-diversion-success bs s v outd outr)
check-diversion-success ((p , adaptive f) ∷ bs) s v (p-s-v≡false , outd) (q-s≡false , outr) =
  assert-not p-s-v≡false then catch-snd fail (check-diversion-success bs s v outd outr)

case-soundness-reentry :
  (bs bs' : List Branch) (R : ℙ (S × V)) (R' : ℙ (S × S × V)) (cont : S → Par S) (ReentryCond : ℙ (S × V)) →
  BranchSound R R' bs bs' ReentryCond → RangeDisjoint bs bs' →
  (s : S) (v : V) → R (s , v) → NormalCaseDomain bs (s , v) → OutOfDomain bs' (s , v) →
  Σ[ s' ∈ S ] ((put-with-adaptation bs bs' s v cont ↦ s') × R' (s' , s , v))
case-soundness-reentry []                      bs' R R' cont ReentryCond sound disj s v sRv ()  out
case-soundness-reentry ((p , normal l q) ∷ bs) bs' R R' cont ReentryCond (b-sound , sound) (b-disj , disj) s v sRv (inj₁ p-s-v≡true) out
  rewrite p-s-v≡true =
  let (s' , l-s-v↦s' , s'R'v , (p-s'-v≡true , outd-s'-v) , q-s'≡true) = b-sound (s , v) (sRv , p-s-v≡true , out)
  in  s' , (l-s-v↦s' >>= assert p-s'-v≡true then assert q-s'≡true then
            check-diversion-success bs' s' v outd-s'-v (b-disj s' q-s'≡true) >>= return refl) , s'R'v
case-soundness-reentry ((p , normal l q) ∷ bs) bs' R R' cont ReentryCond (_ , sound) (_ , disj) s v sRv (inj₂ (p-s-v≡false , dom)) out
  rewrite p-s-v≡false =
  case-soundness-reentry bs ((p , normal l q) ∷ bs') R R' cont ReentryCond sound disj s v sRv dom (p-s-v≡false , out)
case-soundness-reentry ((p , adaptive f) ∷ bs) bs' R R' cont ReentryCond (_ , sound) (_ , disj) s v sRv (p-s-v≡false , dom) out
  rewrite p-s-v≡false =
  case-soundness-reentry bs ((p , adaptive f) ∷ bs') R R' cont ReentryCond sound disj s v sRv dom (p-s-v≡false , out)

case-soundness-main :
  (bs bs' : List Branch) (R : ℙ (S × V)) (R' : ℙ (S × S × V)) (cont : S → Par S) (ReentryCond : ℙ (S × V)) →
  BranchSound R R' bs bs' ReentryCond → RangeDisjoint bs bs' →
  (s : S) (v : V) → R (s , v) → CaseDomain bs (s , v) → OutOfDomain bs' (s , v) →
  ((s'' : S) → R (s'' , v) → ReentryCond (s'' , v) → Σ[ s' ∈ S ] ((cont s'' ↦ s') × R' (s' , s'' , v))) →
  Σ[ s' ∈ S ] ((put-with-adaptation bs bs' s v cont ↦ s') × R' (s' , s , v))
case-soundness-main []             bs' R R' cont ReentryCond sound disj s v sRv ()  out cont-sound
case-soundness-main ((p , normal l q) ∷ bs) bs' R R' cont ReentryCond (b-sound , sound) (b-disj , disj) s v sRv (inj₁ p-s-v≡true) out cont-sound
  rewrite p-s-v≡true =
  let (s' , l-s-v↦s' , s'R'v , (p-s'-v≡true , outd-s'-v) , q-s'≡true) = b-sound (s , v) (sRv , p-s-v≡true , out)
  in  s' , (l-s-v↦s' >>= assert p-s'-v≡true then assert q-s'≡true then
            check-diversion-success bs' s' v outd-s'-v (b-disj s' q-s'≡true) >>= return refl) , s'R'v
case-soundness-main ((p , adaptive f) ∷ bs) bs' R R' cont ReentryCond (lift b-sound , sound) (_ , disj) s v sRv (inj₁ p-s-v≡true) out cont-sound
  rewrite p-s-v≡true = let (f-s-v-R-v , reentry , R'-reflective) = b-sound s v sRv p-s-v≡true
                           (s' , cont↦ , R'-s') = cont-sound (f s v) f-s-v-R-v reentry
                       in  s' , cont↦ , R'-reflective s' R'-s'
case-soundness-main ((p , b) ∷ bs) bs' R R' cont ReentryCond (_ , sound) (_ , disj) s v sRv (inj₂ (p-s-v≡false , dom)) out cont-sound
  rewrite p-s-v≡false =
  case-soundness-main bs ((p , b) ∷ bs') R R' cont ReentryCond sound disj s v sRv dom (p-s-v≡false , out) cont-sound

case-soundness : (bs : List Branch) (R : ℙ (S × V)) (R' : ℙ (S × S × V)) →
                 R ⊆ CaseDomain bs → BranchSound R R' bs [] (NormalCaseDomain bs) → RangeDisjoint bs [] →
                 Sound R (Lens.put (case-lens bs)) R'
case-soundness bs R R' dom sound disj (s , v) sRv =
  case-soundness-main bs [] R R'
    (λ s' → put-with-adaptation bs [] s' v (const fail)) (NormalCaseDomain bs) sound disj s v sRv (dom sRv) tt
    (λ s' s'Rv dom' → case-soundness-reentry bs [] R R' (const fail) (NormalCaseDomain bs) sound disj s' v s'Rv dom' tt)
