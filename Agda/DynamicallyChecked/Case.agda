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

get-branch : Branch → S → Par V
get-branch (p , normal l q) s = assert q s then Lens.get l s >>= λ v → assert p s v then return v
get-branch (p , adaptive f) s = fail

check-diversion : List Branch → S → V → Par ⊤
check-diversion []             s v = return tt
check-diversion ((p , b) ∷ bs) s v = assert-not p s v then
                                     catch (get-branch (p , b) s) (const fail) (check-diversion bs s v)

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

get : List Branch → S → Par V
get []             s = fail
get ((p , b) ∷ bs) s =
  catch (get-branch (p , b) s) return 
        (get bs s >>= λ v → assert-not p s v then return v)

get-revcat : (bs : List Branch) {s : S} {v : V} (bs' : List Branch) → check-diversion bs' s v ↦ tt →
             get bs s ↦ v → get (revcat bs' bs) s ↦ v
get-revcat bs []              _                                         get↦ = get↦
get-revcat bs ((p , b) ∷ bs') (assert-not _           then catch-fst _            ()              ) get↦
get-revcat bs ((p , b) ∷ bs') (assert-not p-s-v≡false then catch-snd get-branch/↦ check-diversion↦) get↦ =
  get-revcat ((p , b) ∷ bs) bs' check-diversion↦ (catch-snd get-branch/↦ (get↦ >>= assert-not p-s-v≡false then return refl))

PutGet-with-adaptation :
  (bs : List Branch) {s : S} {v : V} {s' : S} (bs' : List Branch) →
  {cont : S → Par S} → ({s : S} → cont s ↦ s' → get (revcat bs' bs) s' ↦ v) →
  put-with-adaptation bs bs' s v cont ↦ s' → get (revcat bs' bs) s' ↦ v
PutGet-with-adaptation []                              bs' PutGet-cont ()
PutGet-with-adaptation ((p , b) ∷ bs) {s} {v} bs' PutGet-cont put↦ with p s v
PutGet-with-adaptation ((p , b) ∷ bs) bs' PutGet-cont put↦ | false =
  PutGet-with-adaptation bs ((p , b) ∷ bs') PutGet-cont put↦
PutGet-with-adaptation ((p , normal l q) ∷ bs) {s} {v} bs' PutGet-cont
  (put↦ >>= assert p-s'-v≡true then assert q-s'≡true then check-diversion↦ >>= return refl) | true =
  get-revcat ((p , normal l q) ∷ bs) bs' check-diversion↦
             (catch-fst (assert q-s'≡true then Lens.PutGet l put↦ >>= assert p-s'-v≡true then return refl) (return refl))
PutGet-with-adaptation ((p , adaptive f) ∷ bs) {s} {v} bs' PutGet-cont put↦ | true  = PutGet-cont put↦

PutGet : (bs : List Branch) {s s' : S} {v : V} → put bs s v ↦ s' → get bs s' ↦ v
PutGet bs put↦ = PutGet-with-adaptation bs [] (PutGet-with-adaptation bs [] (λ ())) put↦

GetPut-with-adaptation :
  (bs : List Branch) {s : S} {v : V} {f : S → Par S}
  (bs' : List Branch) → check-diversion bs' s v ↦ tt →
  get bs s ↦ v → put-with-adaptation bs bs' s v f ↦ s
GetPut-with-adaptation []                     bs' check-diversion↦ ()
GetPut-with-adaptation ((p , b) ∷ bs) {s} {v} bs' check-diversion↦ get↦ with p s v | inspect (p s) v
GetPut-with-adaptation ((p , normal l q) ∷ bs) bs' check-diversion↦
  (catch-fst (assert _ then get↦ >>= assert p-s-v≡true then return refl) (return refl)) | false | [ p-s-v≡false ]
  with trans (sym p-s-v≡false) p-s-v≡true
GetPut-with-adaptation ((p , normal l q) ∷ bs) bs' check-diversion↦
  (catch-fst (assert _ then get↦ >>= assert p-s-v≡true then return refl) (return refl)) | false | [ p-s-v≡false ] | ()
GetPut-with-adaptation ((p , adaptive f) ∷ bs) bs' check-diversion↦ (catch-fst () _) | false | _
GetPut-with-adaptation ((p , b) ∷ bs) bs' check-diversion↦
  (catch-snd get-branch/↦ (get↦ >>= assert-not p-s-v≡false then return refl)) | false | _ =
  GetPut-with-adaptation bs ((p , b) ∷ bs') (assert-not p-s-v≡false then catch-snd get-branch/↦ check-diversion↦) get↦
GetPut-with-adaptation ((p , normal l q) ∷ bs) bs' check-diversion↦
  (catch-fst (assert q-s≡true then l-get↦ >>= assert p-s-v≡true then return refl) (return refl)) | true | _ =
  Lens.GetPut l l-get↦ >>= assert p-s-v≡true then assert q-s≡true then check-diversion↦ >>= return refl
GetPut-with-adaptation ((p , normal l q) ∷ bs) bs' check-diversion↦
  (catch-snd _ (get↦ >>= assert-not p-s-v≡false then return refl)) | true | [ p-s-v≡true ]
  with trans (sym p-s-v≡false) p-s-v≡true
GetPut-with-adaptation ((p , normal l q) ∷ bs) bs' check-diversion↦
  (catch-snd _ (get↦ >>= assert-not p-s-v≡false then return refl)) | true | [ p-s-v≡true ] | ()
GetPut-with-adaptation ((p , adaptive f) ∷ bs) bs' check-diversion↦ (catch-fst () _) | true | _
GetPut-with-adaptation ((p , adaptive f) ∷ bs) bs' check-diversion↦
  (catch-snd _ (get↦ >>= assert-not p-s-v≡false then return refl)) | true | [ p-s-v≡true ]
  with trans (sym p-s-v≡false) p-s-v≡true
GetPut-with-adaptation ((p , adaptive f) ∷ bs) bs' check-diversion↦
  (catch-snd _ (get↦ >>= assert-not p-s-v≡false then return refl)) | true | [ p-s-v≡true ] | ()

GetPut : (bs : List Branch) {s : S} {v : V} {f : S → Par S} → get bs s ↦ v → put bs s v ↦ s
GetPut bs = GetPut-with-adaptation bs [] (return refl)

case-lens : List Branch → S ⇆ V
case-lens bs = record { put = put bs; get = get bs; PutGet = PutGet bs; GetPut = GetPut bs {f = const fail} }
