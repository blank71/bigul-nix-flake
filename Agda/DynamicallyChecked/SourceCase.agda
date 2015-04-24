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

put-with-adaptation : List Branch → S → V → (S → Par S) → Par S
put-with-adaptation []              s v f = fail
put-with-adaptation ((p , bt) ∷ bs) s v f =
  p s >>= λ b → if b then elimBranchType (λ lens → Lens.put lens s v >>= λ s' → p s' >>= λ b' → assert b' then return s')
                                         (λ u → u s >>= f) bt
                     else put-with-adaptation bs s v f >>= λ s' → p s' >>= λ b' → assert not b' then return s'

put : List Branch → S → V → Par S
put bs s v = put-with-adaptation bs s v (λ s' → put-with-adaptation bs s' v (const fail))

get : List Branch → S → Par V
get []              s = fail
get ((p , bt) ∷ bs) s = p s >>= λ b → if b then elimBranchType (λ lens → Lens.get lens s) (const fail) bt
                                           else get bs s

UnmatchedBranches : List Branch → S → Set₁
UnmatchedBranches []             s = ⊤
UnmatchedBranches ((p , b) ∷ bs) s = (p s ↦ false) × UnmatchedBranches bs s

get-revcat : (bs : List Branch) {s : S} {v : V} (bs' : List Branch) → UnmatchedBranches bs' s →
             get bs s ↦ v → get (revcat bs' bs) s ↦ v
get-revcat bs []                     ub  get↦ = get↦
get-revcat bs (b ∷ bs') (p-s↦false , ub) get↦ = get-revcat (b ∷ bs) bs' ub (p-s↦false >>= get↦)

PutGet-with-adaptation' :
  (bs : List Branch) {s : S} {v : V} {s' : S} → put-with-adaptation bs s v (const fail) ↦ s' → get bs s' ↦ v
PutGet-with-adaptation' []                       ()
PutGet-with-adaptation' ((p , normal lens) ∷ bs)
  (_>>=_ {x = false} p-s↦false (put↦s' >>= (_>>=_ {x = false} p-s'↦false (assert _ then return refl)))) =
  p-s'↦false >>= PutGet-with-adaptation' bs put↦s'
PutGet-with-adaptation' ((p , normal lens) ∷ bs)
  (_>>=_ {x = false} p-s↦false (put↦s' >>= (_>>=_ {x = true} p-s'↦true (assert () then _))))
PutGet-with-adaptation' ((p , normal lens) ∷ bs)
  (_>>=_ {x = true } p-s↦true (lens-put-s-v↦s' >>= p-s'↦true >>= assert refl then return refl)) =
  p-s'↦true >>= Lens.PutGet lens lens-put-s-v↦s'
PutGet-with-adaptation' ((p , adaptive u ) ∷ bs)
  (_>>=_ {x = false} p-s↦ (put↦ >>= (_>>=_ {x = false} p-s'↦ (assert _ then return refl)))) =
  p-s'↦ >>= PutGet-with-adaptation' bs put↦
PutGet-with-adaptation' ((p , adaptive u ) ∷ bs)
  (_>>=_ {x = false} p-s↦ (put↦ >>= (_>>=_ {x = true} p-s'↦ (assert () then _))))
PutGet-with-adaptation' ((p , adaptive u ) ∷ bs) (_>>=_ {x = true} p-s↦ (_ >>= ()))

PutGet-with-adaptation :
  (bs : List Branch) {s : S} {v : V} {s' : S} (bs' : List Branch) → UnmatchedBranches bs' s' →
  put-with-adaptation bs s v (λ s'' → put-with-adaptation (revcat bs' bs) s'' v (const fail)) ↦ s' →
  get (revcat bs' bs) s' ↦ v
PutGet-with-adaptation []                       bs' ub ()
PutGet-with-adaptation ((p , normal lens) ∷ bs) bs' ub
  (_>>=_ {x = false} p-s↦ (put↦ >>= (_>>=_ {x = false} p-s'↦false (assert _ then return refl)))) =
  PutGet-with-adaptation bs ((p , normal lens) ∷ bs') (p-s'↦false , ub) put↦
PutGet-with-adaptation ((p , normal lens) ∷ bs) bs' ub
  (_>>=_ {x = false} p-s↦ (put↦ >>= (_>>=_ {x = true} p-s'↦true (assert () then _))))
PutGet-with-adaptation ((p , normal lens) ∷ bs) bs' ub
  (_>>=_ {x = true} p-s↦ (lens-put↦ >>= p-s'↦true >>= assert refl then return refl)) =
  get-revcat ((p , normal lens) ∷ bs) bs' ub (p-s'↦true >>= Lens.PutGet lens lens-put↦)
PutGet-with-adaptation ((p , adaptive u ) ∷ bs) bs' ub
  (_>>=_ {x = false} p-s↦false (put↦ >>= (_>>=_ {x = false} p-s'↦false (assert _ then return refl)))) =
  PutGet-with-adaptation bs ((p , adaptive u) ∷ bs') (p-s'↦false , ub) put↦
PutGet-with-adaptation ((p , adaptive u ) ∷ bs) bs' ub
  (_>>=_ {x = false} p-s↦false (put↦ >>= (_>>=_ {x = true} p-s'↦true (assert () then _))))
PutGet-with-adaptation ((p , adaptive u ) ∷ bs) bs' ub (_>>=_ {x = true} p-s↦ (u↦ >>= put↦)) =
  PutGet-with-adaptation' (revcat bs' ((p , adaptive u) ∷ bs)) put↦

PutGet : (bs : List Branch) {s : S} {v : V} {s' : S} → put bs s v ↦ s' → get bs s' ↦ v
PutGet bs = PutGet-with-adaptation bs [] tt

GetPut-with-adaptation : (bs : List Branch) {f : S → Par S} {s : S} {v : V} →
                         get bs s ↦ v → put-with-adaptation bs s v f ↦ s
GetPut-with-adaptation []                       ()
GetPut-with-adaptation ((p , normal lens) ∷ bs) (_>>=_ {x = false} p-s↦false get↦) =
  p-s↦false >>= GetPut-with-adaptation bs get↦ >>= p-s↦false >>= assert refl then return refl
GetPut-with-adaptation ((p , normal lens) ∷ bs) (_>>=_ {x = true} p-s↦true lens-get↦) =
  p-s↦true >>= Lens.GetPut lens lens-get↦ >>= p-s↦true >>= assert refl then return refl
GetPut-with-adaptation ((p , adaptive u ) ∷ bs) (_>>=_ {x = false} p-s↦false get↦) =
  p-s↦false >>= GetPut-with-adaptation bs get↦ >>= p-s↦false >>= assert refl then return refl
GetPut-with-adaptation ((p , adaptive u ) ∷ bs) (_>>=_ {x = true} p-s↦ ())

GetPut : (bs : List Branch) {f : S → Par S} {s : S} {v : V} → get bs s ↦ v → put bs s v ↦ s
GetPut bs = GetPut-with-adaptation bs

caseS-lens : List Branch → S ⇆ V
caseS-lens bs = record
  { put = put bs; get = get bs; PutGet = PutGet bs;
    GetPut = λ {_} {v} → GetPut bs {λ s' → put-with-adaptation bs s' v (const fail)} }
