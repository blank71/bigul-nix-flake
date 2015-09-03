module DynamicallyChecked.SourceCase (S V : Set) where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Level
open import Function
open import Data.Bool
open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality


data BranchType : Set₁ where
  normal   : (S ⇆ V) → BranchType
  adaptive : (S → Par S) → BranchType

Branch : Set₁
Branch = (S → Par Bool) × BranchType

elimBranchType : {l : Level} {A : Set l} → ((S ⇆ V) → A) → ((S → Par S) → A) → BranchType → A
elimBranchType f g (normal   l) = f l
elimBranchType f g (adaptive u) = g u

check-diversion : List Branch → S → Par ⊤
check-diversion [] s = return tt
check-diversion ((p , _) ∷ bs) s = p s >>= λ b → assert not b then check-diversion bs s

put-with-adaptation : List Branch → List Branch → S → V → (S → Par S) → Par S
put-with-adaptation []              bs' s v f = fail
put-with-adaptation ((p , bt) ∷ bs) bs' s v f =
  p s >>= λ b →
  if b then elimBranchType
              (λ lens → Lens.put lens s v >>= λ s' → p s' >>= λ b' → assert b' then check-diversion bs' s' >> return s')
              (λ u → u s >>= f) bt
       else put-with-adaptation bs ((p , bt) ∷ bs') s v f

put : List Branch → S → V → Par S
put bs s v = put-with-adaptation bs [] s v (λ s' → put-with-adaptation bs [] s' v (const fail))

get : List Branch → S → Par V
get []              s = fail
get ((p , bt) ∷ bs) s = p s >>= λ b → if b then elimBranchType (λ lens → Lens.get lens s) (const fail) bt
                                           else get bs s

get-revcat : (bs : List Branch) {s : S} {v : V} (bs' : List Branch) → check-diversion bs' s ↦ tt →
             get bs s ↦ v → get (revcat bs' bs) s ↦ v
get-revcat bs []               _    get↦ = get↦
get-revcat bs ((p , bt) ∷ bs') (_>>=_ {x = true } p-s↦true  (assert () then _              )) get↦
get-revcat bs ((p , bt) ∷ bs') (_>>=_ {x = false} p-s↦false (assert _ then check-diversion↦)) get↦ =
  get-revcat ((p , bt) ∷ bs) bs' check-diversion↦ (p-s↦false >>= get↦)

PutGet-with-adaptation :
  (bs : List Branch) {s : S} {v : V} {s' : S} (bs' : List Branch) →
  {cont : S → Par S} → ({s s' : S} → cont s ↦ s' → get (revcat bs' bs) s' ↦ v) →
  put-with-adaptation bs bs' s v cont ↦ s' → get (revcat bs' bs) s' ↦ v
PutGet-with-adaptation []                      bs' PutGet-cont ()
PutGet-with-adaptation ((p , bt)         ∷ bs) bs' PutGet-cont (_>>=_ {x = false} p-s↦false put↦) =
  PutGet-with-adaptation bs ((p , bt) ∷ bs') PutGet-cont put↦
PutGet-with-adaptation ((p , normal   l) ∷ bs) bs' PutGet-cont
  (_>>=_ {x = true } p-s↦true (put-s-v↦s' >>= p-s'↦true >>= assert refl then (check-diversion↦ >>= return refl))) =
  get-revcat ((p , normal l) ∷ bs) bs' check-diversion↦ (p-s'↦true >>= Lens.PutGet l put-s-v↦s')
PutGet-with-adaptation ((p , adaptive u) ∷ bs) bs' PutGet-cont (_>>=_ {x = true } p-s↦true  (u↦ >>= cont↦)) =
  PutGet-cont cont↦

PutGet : (bs : List Branch) {s : S} {v : V} {s' : S} → put bs s v ↦ s' → get bs s' ↦ v
PutGet bs = PutGet-with-adaptation bs [] (PutGet-with-adaptation bs [] (λ ()))

GetPut-with-adaptation : (bs : List Branch) {f : S → Par S} {s : S} {v : V}
                         (bs' : List Branch) → check-diversion bs' s ↦ tt →
                         get bs s ↦ v → put-with-adaptation bs bs' s v f ↦ s
GetPut-with-adaptation []                      bs' check-diversion↦ ()
GetPut-with-adaptation ((p , bt        ) ∷ bs) bs' check-diversion↦ (_>>=_ {x = false} p-s↦false get↦) =
  p-s↦false >>= GetPut-with-adaptation bs ((p , bt) ∷ bs') (p-s↦false >>= assert refl then check-diversion↦) get↦
GetPut-with-adaptation ((p , normal   l) ∷ bs) bs' check-diversion↦ (_>>=_ {x = true } p-s↦true  get↦) =
  p-s↦true >>= Lens.GetPut l get↦ >>= p-s↦true >>= assert refl then (check-diversion↦ >>= return refl)
GetPut-with-adaptation ((p , adaptive u) ∷ bs) bs' check-diversion↦ (_>>=_ {x = true } p-s↦true  ()  )

GetPut : (bs : List Branch) {f : S → Par S} {s : S} {v : V} → get bs s ↦ v → put bs s v ↦ s
GetPut bs = GetPut-with-adaptation bs [] (return refl)

caseS-lens : List Branch → S ⇆ V
caseS-lens bs = record
  { put = put bs; get = get bs; PutGet = PutGet bs;
    GetPut = λ {_} {v} → GetPut bs {λ s' → put-with-adaptation bs [] s' v (const fail)} }
