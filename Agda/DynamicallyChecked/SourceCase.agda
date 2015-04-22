module DynamicallyChecked.SourceCase (S V : Set) where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Level
open import Function
open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality


data BranchType (S' : Set) : Set₁ where
  normal   : (S' ⇆ V) → BranchType S'
  adaptive : (S' → Par S) → BranchType S'

Branch : Set₁
Branch = Σ[ S' ∈ Set ] (S ⇆ S') × BranchType S'

elimBranchType : {S' : Set} {l : Level} {A : Set l} → ((S' ⇆ V) → A) → ((S' → Par S) → A) → BranchType S' → A
elimBranchType f g (normal   l) = f l
elimBranchType f g (adaptive u) = g u

put-with-adaptation : List Branch → S → V → (S → Par S) → Par S
put-with-adaptation []                      s v f = fail
put-with-adaptation ((S' , lens , bt) ∷ bs) s v f =
  catch (Lens.get lens s)
        (λ s' → elimBranchType (λ lens' → Lens.put lens' s' v >>= Lens.put lens s) (λ u → u s' >>= f) bt)
        (put-with-adaptation bs s v f >>= λ s' → catch (Lens.get lens s') (const fail) (return s'))

put : List Branch → S → V → Par S
put bs s v = put-with-adaptation bs s v (λ s' → put-with-adaptation bs s' v (const fail))

get : List Branch → S → Par V
get []                      s = fail
get ((S' , lens , bt) ∷ bs) s =
  catch (Lens.get lens s) (elimBranchType Lens.get (const (const fail)) bt) (get bs s)

UnmatchedBranches : List Branch → S → Set₁
UnmatchedBranches []                     s = ⊤
UnmatchedBranches ((S' , lens , b) ∷ bs) s = FailedCompSeq (Lens.get lens s) × UnmatchedBranches bs s

get-revcat : (bs : List Branch) {s : S} {v : V} (bs' : List Branch) → UnmatchedBranches bs' s →
             get bs s ↦ v → get (revcat bs' bs) s ↦ v
get-revcat bs []                      ub  get↦ = get↦
get-revcat bs (b ∷ bs') (lens-get↦ᶠ , ub) get↦ = get-revcat (b ∷ bs) bs' ub (catch-snd lens-get↦ᶠ get↦)

PutGet-with-adaptation' :
  (bs : List Branch) {s : S} {v : V} {s' : S} → put-with-adaptation bs s v (const fail) ↦ s' → get bs s' ↦ v
PutGet-with-adaptation' []                                ()
PutGet-with-adaptation' ((S' , lens , normal lens') ∷ bs) (catch-fst lens-get↦ (lens'-put↦ >>= lens-put↦)) =
  catch-fst (Lens.PutGet lens lens-put↦) (Lens.PutGet lens' lens'-put↦)
PutGet-with-adaptation' ((S' , lens , normal lens') ∷ bs) (catch-snd _ (_ >>= catch-fst _ ()))
PutGet-with-adaptation' ((S' , lens , normal lens') ∷ bs)
  (catch-snd lens-get-s↦ᶠ (put-with-adaptation↦ >>= catch-snd lens-get-s'↦ᶠ (return refl))) =
  catch-snd lens-get-s'↦ᶠ (PutGet-with-adaptation' bs put-with-adaptation↦)
PutGet-with-adaptation' ((S' , lens , adaptive u  ) ∷ bs) (catch-fst _ (_ >>= ()))
PutGet-with-adaptation' ((S' , lens , adaptive u  ) ∷ bs) (catch-snd x (_ >>= catch-fst _ ()))
PutGet-with-adaptation' ((S' , lens , adaptive u  ) ∷ bs)
  (catch-snd lens-get-s↦ᶠ (put-with-adaptation↦ >>= catch-snd lens-get-s'↦ᶠ (return refl))) =
  catch-snd lens-get-s'↦ᶠ (PutGet-with-adaptation' bs put-with-adaptation↦)

PutGet-with-adaptation :
  (bs : List Branch) {s : S} {v : V} {s' : S} (bs' : List Branch) → UnmatchedBranches bs' s' →
  put-with-adaptation bs s v (λ s'' → put-with-adaptation (revcat bs' bs) s'' v (const fail)) ↦ s' →
  get (revcat bs' bs) s' ↦ v
PutGet-with-adaptation []                                bs' ub ()
PutGet-with-adaptation ((S' , lens , normal lens') ∷ bs) bs' ub (catch-fst lens-get↦ (lens'-put↦ >>= lens-put↦)) =
  get-revcat ((S' , lens , normal lens') ∷ bs) bs' ub
    (catch-fst (Lens.PutGet lens lens-put↦) (Lens.PutGet lens' lens'-put↦))
PutGet-with-adaptation ((S' , lens , normal lens') ∷ bs) bs' ub
  (catch-snd lens-get↦ᶠ (put-with-adaptation↦ >>= catch-fst _ ()))
PutGet-with-adaptation ((S' , lens , normal lens') ∷ bs) bs' ub
  (catch-snd lens-get-s↦ᶠ (put-with-adaptation↦ >>= catch-snd lens-get-s'↦ᶠ (return refl))) =
  PutGet-with-adaptation bs ((S' , lens , normal lens') ∷ bs') (lens-get-s'↦ᶠ , ub) put-with-adaptation↦
PutGet-with-adaptation ((S' , lens , adaptive u  ) ∷ bs) bs' ub (catch-fst lens-get↦ (u↦ >>= put-with-adaptation↦)) =
  PutGet-with-adaptation' (revcat bs' ((S' , lens , adaptive u) ∷ bs)) put-with-adaptation↦
PutGet-with-adaptation ((S' , lens , adaptive u  ) ∷ bs) bs' ub
  (catch-snd lens-get-s↦ᶠ (put-with-adaptation↦ >>= catch-fst lens-get↦ ()))
PutGet-with-adaptation ((S' , lens , adaptive u  ) ∷ bs) bs' ub
  (catch-snd lens-get-s↦ᶠ (put-with-adaptation↦ >>= catch-snd lens-get-s'↦ᶠ (return refl))) =
  PutGet-with-adaptation bs ((S' , lens , adaptive u) ∷ bs') (lens-get-s'↦ᶠ , ub) put-with-adaptation↦

PutGet : (bs : List Branch) {s : S} {v : V} {s' : S} → put bs s v ↦ s' → get bs s' ↦ v
PutGet bs = PutGet-with-adaptation bs [] tt

GetPut-with-adaptation : (bs : List Branch) {f : S → Par S} {s : S} {v : V} →
                         get bs s ↦ v → put-with-adaptation bs s v f ↦ s
GetPut-with-adaptation []                                ()
GetPut-with-adaptation ((S' , lens , normal lens') ∷ bs) (catch-fst lens-get↦ lens'-get↦) =
  catch-fst lens-get↦ (Lens.GetPut lens' lens'-get↦ >>= Lens.GetPut lens lens-get↦)
GetPut-with-adaptation ((S' , lens , normal lens') ∷ bs) (catch-snd lens-get↦ᶠ get↦) =
  catch-snd lens-get↦ᶠ (GetPut-with-adaptation bs get↦ >>= catch-snd lens-get↦ᶠ (return refl))
GetPut-with-adaptation ((S' , lens , adaptive u  ) ∷ bs) (catch-fst lens-get↦ ())
GetPut-with-adaptation ((S' , lens , adaptive u  ) ∷ bs) (catch-snd lens-get↦ᶠ get↦) =
  catch-snd lens-get↦ᶠ (GetPut-with-adaptation bs get↦ >>= catch-snd lens-get↦ᶠ (return refl))

GetPut : (bs : List Branch) {f : S → Par S} {s : S} {v : V} → get bs s ↦ v → put bs s v ↦ s
GetPut bs = GetPut-with-adaptation bs

caseS-lens : List Branch → S ⇆ V
caseS-lens bs = record
  { put = put bs; get = get bs; PutGet = PutGet bs;
    GetPut = λ {_} {v} → GetPut bs {λ s' → put-with-adaptation bs s' v (const fail)} }
