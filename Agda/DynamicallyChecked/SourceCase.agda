module DynamicallyChecked.SourceCase (S V : Set) where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Level
open import Function
open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality


data BranchType : Set₁ where
  normal   : (S ⇆ V) → BranchType
  adaptive : (S → Par S) → BranchType

Branch : Set₁
Branch = (S → Par ⊤) × BranchType

elimBranchType : {l : Level} {A : Set l} → ((S ⇆ V) → A) → ((S → Par S) → A) → BranchType → A
elimBranchType f g (normal   l) = f l
elimBranchType f g (adaptive u) = g u

put-with-adaptation : List Branch → S → V → (S → Par S) → Par S
put-with-adaptation []              s v f = fail
put-with-adaptation ((p , bt) ∷ bs) s v f =
  catch (p s) (λ _ → elimBranchType (λ lens → Lens.put lens s v >>= λ s' → p s' >> return s') (λ u → u s >>= f) bt)
        (put-with-adaptation bs s v f >>= λ s' → catch (p s') (const fail) (return s'))

put : List Branch → S → V → Par S
put bs s v = put-with-adaptation bs s v (λ s' → put-with-adaptation bs s' v (const fail))

get : List Branch → S → Par V
get []              s = fail
get ((p , bt) ∷ bs) s = catch (p s) (λ _ → elimBranchType (λ lens → Lens.get lens s) (const fail) bt) (get bs s)

UnmatchedBranches : List Branch → S → Set₁
UnmatchedBranches []             s = ⊤
UnmatchedBranches ((p , b) ∷ bs) s = FailedCompSeq (p s) × UnmatchedBranches bs s

get-revcat : (bs : List Branch) {s : S} {v : V} (bs' : List Branch) → UnmatchedBranches bs' s →
             get bs s ↦ v → get (revcat bs' bs) s ↦ v
get-revcat bs []                      ub  get↦ = get↦
get-revcat bs (b ∷ bs') (lens-get↦ᶠ , ub) get↦ = get-revcat (b ∷ bs) bs' ub (catch-snd lens-get↦ᶠ get↦)

PutGet-with-adaptation' :
  (bs : List Branch) {s : S} {v : V} {s' : S} → put-with-adaptation bs s v (const fail) ↦ s' → get bs s' ↦ v
PutGet-with-adaptation' []                       ()
PutGet-with-adaptation' ((p , normal lens) ∷ bs) (catch-fst p-s↦ (lens-put↦ >>= p-s'↦ >>= return refl)) =
  catch-fst p-s'↦ (Lens.PutGet lens lens-put↦)
PutGet-with-adaptation' ((p , normal lens) ∷ bs) (catch-snd _ (_ >>= catch-fst _ ()))
PutGet-with-adaptation' ((p , normal lens) ∷ bs) (catch-snd p-s↦ᶠ (put↦ >>= catch-snd p-s'↦ᶠ (return refl))) =
  catch-snd p-s'↦ᶠ (PutGet-with-adaptation' bs put↦)
PutGet-with-adaptation' ((p , adaptive u ) ∷ bs) (catch-fst _ (_ >>= ()))
PutGet-with-adaptation' ((p , adaptive u ) ∷ bs) (catch-snd x (_ >>= catch-fst _ ()))
PutGet-with-adaptation' ((p , adaptive u ) ∷ bs) (catch-snd p-s↦ᶠ (put↦ >>= catch-snd p-s'↦ᶠ (return refl))) =
  catch-snd p-s'↦ᶠ (PutGet-with-adaptation' bs put↦)

PutGet-with-adaptation :
  (bs : List Branch) {s : S} {v : V} {s' : S} (bs' : List Branch) → UnmatchedBranches bs' s' →
  put-with-adaptation bs s v (λ s'' → put-with-adaptation (revcat bs' bs) s'' v (const fail)) ↦ s' →
  get (revcat bs' bs) s' ↦ v
PutGet-with-adaptation []                       bs' ub ()
PutGet-with-adaptation ((p , normal lens) ∷ bs) bs' ub (catch-fst p-s↦ (lens-put↦ >>= p-s'↦ >>= return refl)) =
  get-revcat ((p , normal lens) ∷ bs) bs' ub (catch-fst p-s'↦ (Lens.PutGet lens lens-put↦))
PutGet-with-adaptation ((p , normal lens) ∷ bs) bs' ub (catch-snd lens-get↦ᶠ (put↦ >>= catch-fst _ ()))
PutGet-with-adaptation ((p , normal lens) ∷ bs) bs' ub (catch-snd p-s↦ᶠ (put↦ >>= catch-snd p-s'↦ᶠ (return refl))) =
  PutGet-with-adaptation bs ((p , normal lens) ∷ bs') (p-s'↦ᶠ , ub) put↦
PutGet-with-adaptation ((p , adaptive u ) ∷ bs) bs' ub (catch-fst p↦ (u↦ >>= put↦)) =
  PutGet-with-adaptation' (revcat bs' ((p , adaptive u) ∷ bs)) put↦
PutGet-with-adaptation ((p , adaptive u ) ∷ bs) bs' ub (catch-snd p-s↦ᶠ (put↦ >>= catch-fst p-s'↦ ()))
PutGet-with-adaptation ((p , adaptive u ) ∷ bs) bs' ub (catch-snd p-s↦ᶠ (put↦ >>= catch-snd p-s'↦ᶠ (return refl))) =
  PutGet-with-adaptation bs ((p , adaptive u) ∷ bs') (p-s'↦ᶠ , ub) put↦

PutGet : (bs : List Branch) {s : S} {v : V} {s' : S} → put bs s v ↦ s' → get bs s' ↦ v
PutGet bs = PutGet-with-adaptation bs [] tt

GetPut-with-adaptation : (bs : List Branch) {f : S → Par S} {s : S} {v : V} →
                         get bs s ↦ v → put-with-adaptation bs s v f ↦ s
GetPut-with-adaptation []                       ()
GetPut-with-adaptation ((p , normal lens) ∷ bs) (catch-fst p↦ lens-get↦) =
  catch-fst p↦ (Lens.GetPut lens lens-get↦ >>= p↦ >>= return refl)
GetPut-with-adaptation ((p , normal lens) ∷ bs) (catch-snd p↦ᶠ get↦) =
  catch-snd p↦ᶠ (GetPut-with-adaptation bs get↦ >>= catch-snd p↦ᶠ (return refl))
GetPut-with-adaptation ((p , adaptive u ) ∷ bs) (catch-fst p↦ ())
GetPut-with-adaptation ((p , adaptive u ) ∷ bs) (catch-snd p↦ᶠ get↦) =
  catch-snd p↦ᶠ (GetPut-with-adaptation bs get↦ >>= catch-snd p↦ᶠ (return refl))

GetPut : (bs : List Branch) {f : S → Par S} {s : S} {v : V} → get bs s ↦ v → put bs s v ↦ s
GetPut bs = GetPut-with-adaptation bs

caseS-lens : List Branch → S ⇆ V
caseS-lens bs = record
  { put = put bs; get = get bs; PutGet = PutGet bs;
    GetPut = λ {_} {v} → GetPut bs {λ s' → put-with-adaptation bs s' v (const fail)} }
