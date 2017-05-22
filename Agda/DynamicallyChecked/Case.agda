module DynamicallyChecked.Case (S V : Set) where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Lens

open import Agda.Primitive
open import Function
open import Data.Product
open import Data.Bool
open import Data.List
open import Relation.Binary.PropositionalEquality


data BranchType : Set₁ where
  normal   : (S ⇆ V) → (S → Bool) → BranchType
  adaptive : (S → V → S) → BranchType

elimBranchType : {l : Level} {A : Set l} → ((S ⇆ V) → (S → Bool) → A) → ((S → V → S) → A) → BranchType → A
elimBranchType g h (normal l q) = g l q
elimBranchType g h (adaptive f) = h f

isNormal : BranchType → Bool
isNormal = elimBranchType (λ _ _ → true) (λ _ → false)

Branch : Set₁
Branch = (S → V → Bool) × BranchType

check-diversion : List Branch → S → V → Par ⊤
check-diversion []                      s v = return tt
check-diversion ((p , normal l q) ∷ bs) s v = assert-not p s v then assert-not q s then check-diversion bs s v
check-diversion ((p , adaptive f) ∷ bs) s v = assert-not p s v then check-diversion bs s v

put-with-adaptation : List Branch → List Branch → S → V → (S → Par S) → Par S
put-with-adaptation []             bs' s v cont = fail
put-with-adaptation ((p , b) ∷ bs) bs' s v cont = 
  if p s v then elimBranchType (λ l q → Lens.put l s v >>= λ s' →
                                        assert p s' v then assert q s' then
                                        check-diversion bs' s' v >> return s')
                               (λ f → cont (f s v)) b
           else put-with-adaptation bs ((p , b) ∷ bs') s v cont

put : List Branch → S → V → Par S
put bs s v = put-with-adaptation bs [] s v (λ s' → put-with-adaptation bs [] s' v (const fail))

fail-continuation : (bs bs' : List Branch) {s' s : S} {v : V} → put-with-adaptation bs bs' s v (const fail) ↦ s' →
                    {cont : S → Par S} → put-with-adaptation bs bs' s v cont ↦ s'
fail-continuation []                      bs'             () 
fail-continuation ((p , b) ∷ bs)          bs' {s = s} {v} c  with p s v
fail-continuation ((p , b) ∷ bs)          bs'             c  | false = fail-continuation bs ((p , b) ∷ bs') c
fail-continuation ((p , normal l q) ∷ bs) bs'             c  | true  = c
fail-continuation ((p , adaptive f) ∷ bs) bs'             () | true

get : List Branch → S → Par V
get []             s = fail
get ((p , normal l q) ∷ bs) s = if q s then (Lens.get l s >>= λ v → assert p s v then return v) else get bs s >>= λ v → assert-not p s v then return v
get ((p , adaptive f) ∷ bs) s = get bs s >>= λ v → assert-not p s v then return v

get-revcat : (bs : List Branch) {s : S} {v : V} (bs' : List Branch) → check-diversion bs' s v ↦ tt →
             get bs s ↦ v → get (revcat bs' bs) s ↦ v
get-revcat bs []              _                                         get↦ = get↦
get-revcat bs ((p , normal l q) ∷ bs') (assert-not p-s-v≡false then assert-not q-s≡false then check-diversion↦) get↦
  with get-revcat ((p , normal l q) ∷ bs) bs' check-diversion↦
get-revcat bs ((p , normal l q) ∷ bs') (assert-not p-s-v≡false then assert-not q-s≡false then check-diversion↦) get↦
  | k rewrite q-s≡false = k (get↦ >>= assert-not p-s-v≡false then return refl)
get-revcat bs ((p , adaptive f) ∷ bs') (assert-not p-s-v≡false then check-diversion↦) get↦ =
  get-revcat ((p , adaptive f) ∷ bs) bs' check-diversion↦ (get↦ >>= assert-not p-s-v≡false then return refl)

PutGet-with-adaptation :
  (bs : List Branch) {s : S} {v : V} {s' : S} (bs' : List Branch) →
  {cont : S → Par S} → ({s : S} → cont s ↦ s' → get (revcat bs' bs) s' ↦ v) →
  put-with-adaptation bs bs' s v cont ↦ s' → get (revcat bs' bs) s' ↦ v
PutGet-with-adaptation []                              bs' PutGet-cont ()
PutGet-with-adaptation ((p , b) ∷ bs) {s} {v} bs' PutGet-cont put↦ with p s v
PutGet-with-adaptation ((p , b) ∷ bs) bs' PutGet-cont put↦ | false =
  PutGet-with-adaptation bs ((p , b) ∷ bs') PutGet-cont put↦
PutGet-with-adaptation ((p , normal l q) ∷ bs) bs' PutGet-cont
  (put↦ >>= assert p-s'-v≡true then assert q-s'≡true then check-diversion↦ >>= return refl) | true
  with get-revcat ((p , normal l q) ∷ bs) bs' check-diversion↦
PutGet-with-adaptation ((p , normal l q) ∷ bs) {s' = s'} bs' PutGet-cont
  (put↦ >>= assert p-s'-v≡true then assert q-s'≡true then check-diversion↦ >>= return refl) | true | k rewrite q-s'≡true =
  k (Lens.PutGet l put↦ >>= assert p-s'-v≡true then return refl)
PutGet-with-adaptation ((p , adaptive f) ∷ bs) bs' PutGet-cont put↦ | true  = PutGet-cont put↦

PutGet : (bs : List Branch) {s s' : S} {v : V} → put bs s v ↦ s' → get bs s' ↦ v
PutGet bs put↦ = PutGet-with-adaptation bs [] (PutGet-with-adaptation bs [] (λ ())) put↦

GetPut-with-adaptation :
  (bs : List Branch) {s : S} {v : V} {f : S → Par S}
  (bs' : List Branch) → check-diversion bs' s v ↦ tt →
  get bs s ↦ v → put-with-adaptation bs bs' s v f ↦ s
GetPut-with-adaptation []                     bs' check-diversion↦ ()
GetPut-with-adaptation ((p , b) ∷ bs) {s} {v} bs' check-diversion↦ get↦ with p s v | inspect (p s) v
GetPut-with-adaptation ((p , normal l q) ∷ bs) {s} bs' check-diversion↦ get↦
  | false | [ p-s-v≡false ] with q s | inspect q s
GetPut-with-adaptation ((p , normal l q) ∷ bs) bs' check-diversion↦ (get↦ >>= assert-not _ then return refl)
  | false | [ p-s-v≡false ] | false | [ q-s≡false ] =
  GetPut-with-adaptation bs ((p , normal l q) ∷ bs')
    (assert-not p-s-v≡false then assert-not q-s≡false then check-diversion↦) get↦
GetPut-with-adaptation ((p , normal l q) ∷ bs) bs' check-diversion↦ (_ >>= assert p-s-v≡true then return refl)
  | false | [ p-s-v≡false ] | true | _ with trans (sym p-s-v≡true) p-s-v≡false
GetPut-with-adaptation ((p , normal l q) ∷ bs) bs' check-diversion↦ (_ >>= assert p-s-v≡true then return refl)
  | false | [ p-s-v≡false ] | true | _ | ()
GetPut-with-adaptation ((p , adaptive f) ∷ bs) bs' check-diversion↦ (get↦ >>= assert-not _ then return refl)
  | false | [ p-s-v≡false ] =
  GetPut-with-adaptation bs ((p , adaptive f) ∷ bs') (assert-not p-s-v≡false then check-diversion↦) get↦
GetPut-with-adaptation ((p , normal l q) ∷ bs) {s} bs' check-diversion↦ get↦
  | true | [ p-s-v≡true ] with q s | inspect q s
GetPut-with-adaptation ((p , normal l q) ∷ bs) bs' check-diversion↦ (get↦ >>= assert-not p-s-v≡false then return refl)
  | true | [ p-s-v≡true ] | false | [ q-s≡false ] with trans (sym p-s-v≡false) p-s-v≡true
GetPut-with-adaptation ((p , normal l q) ∷ bs) bs' check-diversion↦ (get↦ >>= assert-not p-s-v≡false then return refl)
  | true | [ p-s-v≡true ] | false | [ q-s≡false ] | ()
GetPut-with-adaptation ((p , normal l q) ∷ bs) bs' check-diversion↦ (get↦ >>= assert _ then return refl)
  | true | [ p-s-v≡true ] | true | [ q-s≡true ] =
  Lens.GetPut l get↦ >>= assert p-s-v≡true then assert q-s≡true then check-diversion↦ >>= return refl
GetPut-with-adaptation ((p , adaptive f) ∷ bs) bs' check-diversion↦ (_ >>= assert-not p-s-v≡false then return refl)
  | true | [ p-s-v≡true ] with trans (sym p-s-v≡false) p-s-v≡true
GetPut-with-adaptation ((p , adaptive f) ∷ bs) bs' check-diversion↦ (_ >>= assert-not p-s-v≡false then return refl)
  | true | [ p-s-v≡true ] | ()

GetPut : (bs : List Branch) {s : S} {v : V} {f : S → Par S} → get bs s ↦ v → put bs s v ↦ s
GetPut bs = GetPut-with-adaptation bs [] (return refl)

case-lens : List Branch → S ⇆ V
case-lens bs = record { put = put bs; get = get bs; PutGet = PutGet bs; GetPut = GetPut bs {f = const fail} }
