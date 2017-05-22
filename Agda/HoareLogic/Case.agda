module HoareLogic.Case {S V : Set} where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens
open import DynamicallyChecked.Case S V
open import HoareLogic.Semantics

open import Level
open import Function
open import Data.Bool
open import Data.Product as Product hiding (,_)
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

OutOfRange : List Branch → ℙ S
OutOfRange [] = Π
OutOfRange ((_ , normal _ q) ∷ bs) = (False ∘ q) ∩ OutOfRange bs
OutOfRange ((_ , adaptive _) ∷ bs) = OutOfRange bs

BranchSound : (R : ℙ (S × V)) (R' : ℙ (S × S × V)) → List Branch → List Branch → ℙ (S × V) → Set₁
BranchSound R R' []             bs' ReentryCond = ⊤
BranchSound R R' ((p , b) ∷ bs) bs' ReentryCond =
  let Pre = R ∩ (True ∘ uncurry p) ∩ OutOfDomain (List.map proj₁ bs')
  in  elimBranchType
        (λ l q → Sound Pre (Lens.put l)
                       (R' ∩ (((True ∘ uncurry p) ∩ OutOfDomain (List.map proj₁ bs')) ∘ Product.map id proj₂) ∩
                             (((True ∘ q) ∩ OutOfRange bs') ∘ proj₁)))
        (λ f → Lift ((s : S) (v : V) → Pre (s , v) →
                     (R ∩ ReentryCond) (f s v , v) × ((s' : S) → R' (s' , f s v , v) → R' (s' , s , v)))) b ×
  BranchSound R R' bs ((p , b) ∷ bs') ReentryCond

inCaseDomain : (bs bs' : List Branch) {s' s : S} {v : V} {cont : S → Par S} →
               put-with-adaptation bs bs' s v cont ↦ s' → CaseDomain (List.map proj₁ bs) (s , v)
inCaseDomain []             bs'             ()
inCaseDomain ((p , b) ∷ bs) bs' {s = s} {v} c with p s v
inCaseDomain ((p , b) ∷ bs) bs' {s = s} {v} c | false = inj₂ (inCaseDomain bs ((p , b) ∷ bs') c)
inCaseDomain ((p , b) ∷ bs) bs' {s = s} {v} c | true  = inj₁ refl

inNormalCaseDomain : (bs bs' : List Branch) {s' s : S} {v : V} →
                     put-with-adaptation bs bs' s v (const fail) ↦ s' →
                     NormalCaseDomain (List.map (Product.map id isNormal) bs) (s , v)
inNormalCaseDomain []             bs'             ()
inNormalCaseDomain ((p , b) ∷ bs) bs' {s = s} {v} c with p s v | inspect (p s) v
inNormalCaseDomain ((p , normal l q) ∷ bs) bs' {s = s} {v} c
  | false | [ p-s-v≡false ] = inj₂ (inNormalCaseDomain bs ((p , normal l q) ∷ bs') c)
inNormalCaseDomain ((p , adaptive f) ∷ bs) bs' {s = s} {v} c
  | false | [ p-s-v≡false ] = p-s-v≡false , inNormalCaseDomain bs ((p , adaptive f) ∷ bs') c
inNormalCaseDomain ((p , normal l q) ∷ bs) bs' {s = s} {v} c
  | true  | [ p-s-v≡true  ] = inj₁ p-s-v≡true
inNormalCaseDomain ((p , adaptive f) ∷ bs) bs' {s = s} {v} ()
  | true  | [ p-s-v≡true  ]

check-diversion-success : (bs : List Branch) (s : S) (v : V) →
                          OutOfDomain (List.map proj₁ bs) (s , v) → OutOfRange bs s → check-diversion bs s v ↦ tt
check-diversion-success []                      s v                outd               outr  = return refl
check-diversion-success ((p , normal l q) ∷ bs) s v (p-s-v≡false , outd) (q-s≡false , outr) =
  assert-not p-s-v≡false then assert-not q-s≡false then (check-diversion-success bs s v outd outr)
check-diversion-success ((p , adaptive f) ∷ bs) s v (p-s-v≡false , outd) outr =
  assert-not p-s-v≡false then check-diversion-success bs s v outd outr

check-diversion-inverse : (bs : List Branch) (s : S) (v : V) →
                          check-diversion bs s v ↦ tt → OutOfDomain (List.map proj₁ bs) (s , v) × OutOfRange bs s
check-diversion-inverse []                      s v c = tt , tt
check-diversion-inverse ((p , normal l q) ∷ bs) s v (assert-not p-s-v≡false then assert-not q-s≡false then c) =
  Product.map (p-s-v≡false ,_) (q-s≡false ,_) (check-diversion-inverse bs s v c)
check-diversion-inverse ((p , adaptive f) ∷ bs) s v (assert-not p-s-v≡false then c) =
  Product.map (p-s-v≡false ,_) id (check-diversion-inverse bs s v c)

case-soundness-reentry :
  (bs bs' : List Branch) (R : ℙ (S × V)) (R' : ℙ (S × S × V)) (cont : S → Par S) (ReentryCond : ℙ (S × V)) →
  BranchSound R R' bs bs' ReentryCond →
  (s : S) (v : V) → R (s , v) → NormalDecCaseDomain (List.map (Product.map id isNormal) bs) (s , v) →
  OutOfDomain (List.map proj₁ bs') (s , v) →
  Σ[ s' ∈ S ] ((put-with-adaptation bs bs' s v cont ↦ s') × R' (s' , s , v))
case-soundness-reentry [] bs' R R' cont ReentryCond sound s v Rsv () outd
case-soundness-reentry ((p , normal l q) ∷ bs) bs' R R' cont ReentryCond (b-sound , sound) s v Rsv
  (inj₁ p-s-v≡true) outd rewrite p-s-v≡true
  = let (s' , l-s-v↦s' , s'R'v , (p-s'-v≡true , outd-s'-v) , q-s'≡true , outr-s') = b-sound (s , v) (Rsv , p-s-v≡true , outd)
    in  s' , (l-s-v↦s' >>= assert p-s'-v≡true then assert q-s'≡true then
              check-diversion-success bs' s' v outd-s'-v outr-s' >>= return refl) , s'R'v
case-soundness-reentry ((p , normal l q) ∷ bs) bs' R R' cont ReentryCond (b-sound , sound) s v Rsv
  (inj₂ (p-s-v≡false , dom)) outd rewrite p-s-v≡false
  = case-soundness-reentry bs ((p , normal l q) ∷ bs') R R' cont ReentryCond sound s v Rsv dom (p-s-v≡false , outd)
case-soundness-reentry ((p , adaptive f) ∷ bs) bs' R R' cont ReentryCond (_ , sound) s v Rsv (p-s-v≡false , dom) outd
  rewrite p-s-v≡false
  = case-soundness-reentry bs ((p , adaptive f) ∷ bs') R R' cont ReentryCond sound s v Rsv dom (p-s-v≡false , outd)

case-soundness-main :
  (bs bs' : List Branch) (R : ℙ (S × V)) (R' : ℙ (S × S × V)) (cont : S → Par S) (ReentryCond : ℙ (S × V)) →
  BranchSound R R' bs bs' ReentryCond →
  (s : S) (v : V) → R (s , v) → DecCaseDomain (List.map proj₁ bs) (s , v) → OutOfDomain (List.map proj₁ bs') (s , v) →
  ((s'' : S) → R (s'' , v) → ReentryCond (s'' , v) → Σ[ s' ∈ S ] ((cont s'' ↦ s') × R' (s' , s'' , v))) →
  Σ[ s' ∈ S ] ((put-with-adaptation bs bs' s v cont ↦ s') × R' (s' , s , v))
case-soundness-main []             bs' R R' cont ReentryCond sound s v sRv ()  out cont-sound
case-soundness-main ((p , normal l q) ∷ bs) bs' R R' cont ReentryCond (b-sound , sound) s v sRv (inj₁ p-s-v≡true) out cont-sound
  rewrite p-s-v≡true =
  let (s' , l-s-v↦s' , s'R'v , (p-s'-v≡true , outd-s'-v) , q-s'≡true , outr-s') = b-sound (s , v) (sRv , p-s-v≡true , out)
  in  s' , (l-s-v↦s' >>= assert p-s'-v≡true then assert q-s'≡true then
            check-diversion-success bs' s' v outd-s'-v outr-s' >>= return refl) , s'R'v
case-soundness-main ((p , adaptive f) ∷ bs) bs' R R' cont ReentryCond (lift f-sound , sound) s v sRv (inj₁ p-s-v≡true) out cont-sound
  rewrite p-s-v≡true = let (f-s-v-R-v , reentry) = proj₁ (f-sound _ _ (sRv , p-s-v≡true , out))
                           (s' , cont↦ , R'-s') = cont-sound (f s v) f-s-v-R-v reentry
                       in  s' , cont↦ , proj₂ (f-sound _ _ (sRv , p-s-v≡true , out)) _ R'-s'
case-soundness-main ((p , normal l q) ∷ bs) bs' R R' cont ReentryCond (_ , sound) s v sRv (inj₂ (p-s-v≡false , dom)) out cont-sound
  rewrite p-s-v≡false =
  case-soundness-main bs ((p , normal l q) ∷ bs') R R' cont ReentryCond sound s v sRv dom (p-s-v≡false , out) cont-sound
case-soundness-main ((p , adaptive f) ∷ bs) bs' R R' cont ReentryCond (_ , sound) s v sRv (inj₂ (p-s-v≡false , dom)) out cont-sound
  rewrite p-s-v≡false =
  case-soundness-main bs ((p , adaptive f) ∷ bs') R R' cont ReentryCond sound s v sRv dom (p-s-v≡false , out) cont-sound

case-soundness : (bs : List Branch) (R : ℙ (S × V)) (R' : ℙ (S × S × V)) →
                 BranchSound R R' bs [] (NormalCaseDomain (List.map (Product.map id isNormal) bs)) →
                 R ⊆ CaseDomain (List.map proj₁ bs) → Sound R (Lens.put (case-lens bs)) R'
case-soundness bs R R' sound dom (s , v) sRv =
  case-soundness-main bs [] R R'
    (λ s' → put-with-adaptation bs [] s' v (const fail)) (NormalCaseDomain (List.map (Product.map id isNormal) bs))
              sound s v sRv (toDecCaseDomain (List.map proj₁ bs) (dom sRv)) tt
    (λ s' s'Rv dom' →
       case-soundness-reentry bs [] R R' (const fail) (NormalCaseDomain (List.map (Product.map id isNormal) bs))
         sound s' v s'Rv (toNormalDecCaseDomain (List.map (Product.map id isNormal) bs) dom') tt)

BranchSoundG : (R : ℙ (S × V)) → List Branch → List Branch → Set₁
BranchSoundG R []                      bs' = ⊤
BranchSoundG R ((p , normal l q) ∷ bs) bs' =
  (Σ[ P ∈ ℙ S ] SoundG P (Lens.get l) (R ∩ (True ∘ uncurry p) ∩ OutOfDomain (List.map proj₁ bs'))) ×
  BranchSoundG R bs ((p , normal l q) ∷ bs')
BranchSoundG R ((p , adaptive f) ∷ bs) bs' = BranchSoundG R bs ((p , adaptive f) ∷ bs')

DecRange : (R : ℙ (S × V)) (bs bs' : List Branch) → BranchSoundG R bs bs' → ℙ S
DecRange R []                      bs' _                  = ∅
DecRange R ((p , normal l q) ∷ bs) bs' ((P , _) , soundG) = (P ∩ (True ∘ q)) ∪ ((False ∘ q) ∩ DecRange R bs ((p , normal l q) ∷ bs') soundG)
DecRange R ((p , adaptive f) ∷ bs) bs' soundG             = DecRange R bs ((p , adaptive f) ∷ bs') soundG

Range : (R : ℙ (S × V)) (bs bs' : List Branch) → BranchSoundG R bs bs' → ℙ S
Range R []                      bs' _                  = ∅
Range R ((p , normal l q) ∷ bs) bs' ((P , _) , soundG) = (P ∩ (True ∘ q) ∩ OutOfRange bs') ∪ Range R bs ((p , normal l q) ∷ bs') soundG
Range R ((p , adaptive f) ∷ bs) bs' soundG             = Range R bs ((p , adaptive f) ∷ bs') soundG

toDecRange : (R : ℙ (S × V)) (bs bs' : List Branch) (soundG : BranchSoundG R bs bs') →
             Range R bs bs' soundG ⊆ DecRange R bs bs' soundG ∩ OutOfRange bs'
toDecRange R []                      bs' soundG ()
toDecRange R ((p , normal l q) ∷ bs) bs' ((P , soundG) , soundGs) (inj₁ (ps , q-s≡true , out-bs'-s)) = inj₁ (ps , q-s≡true) , out-bs'-s
toDecRange R ((p , normal l q) ∷ bs) bs' ((P , soundG) , soundGs) {s} (inj₂ range)
  with toDecRange R bs ((p , normal l q) ∷ bs') soundGs range
toDecRange R ((p , normal l q) ∷ bs) bs' ((P , soundG) , soundGs) {s} (inj₂ range)
  | decRange , q-s≡false , out = (inj₂ (q-s≡false , decRange)) , out
toDecRange R ((p , adaptive f) ∷ bs) bs' soundG range = toDecRange R bs ((p , adaptive f) ∷ bs') soundG range

case-soundnessG-main : (bs bs' : List Branch) (R : ℙ (S × V)) (soundG : BranchSoundG R bs bs') →
                       (s : S) → DecRange R bs bs' soundG s →
                       Σ[ v ∈ V ] Lens.get (case-lens bs) s ↦ v × R (s , v) × OutOfDomain (List.map proj₁ bs') (s , v)
case-soundnessG-main []                      bs' R soundG s ()
case-soundnessG-main ((p , normal l q) ∷ bs) bs' R ((P , soundG) , soundGs) s (inj₁ (ps , q-s≡true))
  with soundG s ps
case-soundnessG-main ((p , normal l q) ∷ bs) bs' R ((P , soundG) , soundGs) s (inj₁ (ps , q-s≡true))
  | v , get↦ , Rsv , p-s-v≡true , out rewrite q-s≡true =
  v , (get↦ >>= assert p-s-v≡true then return refl) , Rsv , out
case-soundnessG-main ((p , normal l q) ∷ bs) bs' R ((P , soundG) , soundGs) s (inj₂ (q-s≡false , range-s))
  with case-soundnessG-main bs ((p , normal l q) ∷ bs') R soundGs s range-s
case-soundnessG-main ((p , normal l q) ∷ bs) bs' R ((P , soundG) , soundGs) s (inj₂ (q-s≡false , range-s))
  | v , get↦ , Rsv , p-s-v≡false , out rewrite q-s≡false =
  v , (get↦ >>= assert-not p-s-v≡false then return refl) , Rsv , out
case-soundnessG-main ((p , adaptive f) ∷ bs) bs' R soundG s range-s
  with case-soundnessG-main bs ((p , adaptive f) ∷ bs') R soundG s range-s
case-soundnessG-main ((p , adaptive f) ∷ bs) bs' R soundG s range-s | v , get↦ , Rsv , p-s-v≡false , out =
  v , (get↦ >>= assert-not p-s-v≡false then return refl) , Rsv , out

case-soundnessG : (bs : List Branch) (R : ℙ (S × V)) (soundG : BranchSoundG R bs []) →
                  (P : ℙ S) → P ⊆ Range R bs [] soundG → SoundG P (Lens.get (case-lens bs)) R
case-soundnessG bs R soundG P P⊆ s Ps with case-soundnessG-main bs [] R soundG s (proj₁ (toDecRange R bs [] soundG (P⊆ Ps)))
case-soundnessG bs R soundG P P⊆ s Ps | v , get↦ , Rsv , _ = v , get↦ , Rsv
