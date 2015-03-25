open import DynamicallyChecked.Universe
open import Data.Nat

module DynamicallyChecked.SourceUpdate {n : ℕ} {F : Functor n} where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Data.Product
open import Data.Sum
open import Data.Fin
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


PatLenses :  {G : U n} → Pattern F G → Set₁
PatLenses pat = ⟦ pat ⟧ᴾ (λ G → Σ[ V ∈ Set ] (⟦ G ⟧ (μ F) ⇆ V))

PatLensesViews : {G : U n} (pat : Pattern F G) → PatLenses pat → Set
PatLensesViews var              (V , _)    = V
PatLensesViews (k x           ) tt         = ⊤
PatLensesViews (child pat     ) ls         = PatLensesViews pat ls
PatLensesViews (left pat      ) ls         = PatLensesViews pat ls
PatLensesViews (right pat     ) ls         = PatLensesViews pat ls
PatLensesViews (prod lpat rpat) (ls , ls') = PatLensesViews lpat ls × PatLensesViews rpat ls'
PatLensesViews (elem hpat tpat) (ls , ls') = PatLensesViews hpat ls × PatLensesViews tpat ls'

module SourceUpdateLens where

  puts : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → PatResult pat → PatLensesViews pat ls → Par (PatResult pat)
  puts     var              (V , l)     s        v       = Lens.put l s v
  puts {G} (k x           ) ls          tt       v       = return tt
  puts     (child pat     ) ls          s        v       = puts pat ls s v
  puts     (left pat      ) ls          s        v       = puts pat ls s v
  puts     (right pat     ) ls          s        v       = puts pat ls s v
  puts     (prod lpat rpat) (ls , ls') (s , s') (v , v') = liftPar₂ _,_ (puts lpat ls s v) (puts rpat ls' s' v')
  puts     (elem hpat tpat) (ls , ls') (s , s') (v , v') = liftPar₂ _,_ (puts hpat ls s v) (puts tpat ls' s' v')

  put : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → ⟦ G ⟧ (μ F) → PatLensesViews pat ls → Par (⟦ G ⟧ (μ F))
  put pat ls s v = deconstruct pat s >>= λ s' → liftPar (construct pat) (puts pat ls s' v)

  gets : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → PatResult pat → Par (PatLensesViews pat ls)
  gets var              (V , l)     s       = Lens.get l s
  gets (k x           ) ls          tt      = return tt
  gets (child pat     ) ls          s       = gets pat ls s
  gets (left pat      ) ls          s       = gets pat ls s
  gets (right pat     ) ls          s       = gets pat ls s
  gets (prod lpat rpat) (ls , ls') (s , s') = liftPar₂ _,_ (gets lpat ls s) (gets rpat ls' s')
  gets (elem hpat tpat) (ls , ls') (s , s') = liftPar₂ _,_ (gets hpat ls s) (gets tpat ls' s')

  get : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → ⟦ G ⟧ (μ F) → Par (PatLensesViews pat ls)
  get pat ls = gets pat ls  <=< deconstruct pat

  PutGets : {G : U n} (pat : Pattern F G) (ls : PatLenses pat)
            {s : PatResult pat} {v : PatLensesViews pat ls} {s' : PatResult pat} →
            puts pat ls s v ↦ s' → gets pat ls s' ↦ v
  PutGets var              (V , l)    put↦  = Lens.PutGet l put↦
  PutGets (k x           ) ls         puts↦ = return refl
  PutGets (child pat     ) ls         puts↦ = PutGets pat ls puts↦
  PutGets (left pat      ) ls         puts↦ = PutGets pat ls puts↦
  PutGets (right pat     ) ls         puts↦ = PutGets pat ls puts↦
  PutGets (prod lpat rpat) (ls , ls') (lputs↦ >>= rputs↦ >>= return refl) = PutGets lpat ls lputs↦ >>=
                                                                            PutGets rpat ls' rputs↦ >>= return refl
  PutGets (elem hpat tpat) (ls , ls') (eputs↦ >>= tputs↦ >>= return refl) = PutGets hpat ls eputs↦ >>=
                                                                            PutGets tpat ls' tputs↦ >>= return refl

  PutGet : {G : U n} (pat : Pattern F G) (ls : PatLenses pat)
           {s : ⟦ G ⟧ (μ F)} {v : PatLensesViews pat ls} {s' : ⟦ G ⟧ (μ F)} →
           put pat ls s v ↦ s' → get pat ls s' ↦ v
  PutGet pat ls (deconstruct↦ >>= puts↦ >>= return refl) = construct-deconstruct-inverse pat _ >>= PutGets pat ls puts↦

  GetPuts : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) {s : PatResult pat} {v : PatLensesViews pat ls} →
            gets pat ls s ↦ v → puts pat ls s v ↦ s
  GetPuts var              (V , l)    get↦  = Lens.GetPut l get↦
  GetPuts (k x           ) ls         gets↦ = return refl
  GetPuts (child pat     ) ls         gets↦ = GetPuts pat ls gets↦
  GetPuts (left pat      ) ls         gets↦ = GetPuts pat ls gets↦
  GetPuts (right pat     ) ls         gets↦ = GetPuts pat ls gets↦
  GetPuts (prod lpat rpat) (ls , ls') (lgets↦ >>= rgets↦ >>= return refl) =
    GetPuts lpat ls lgets↦ >>= GetPuts rpat ls' rgets↦ >>= return refl
  GetPuts (elem hpat tpat) (ls , ls') (egets↦ >>= tgets↦ >>= return refl) = 
    GetPuts hpat ls egets↦ >>= GetPuts tpat ls' tgets↦ >>= return refl

  GetPut : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) {s : ⟦ G ⟧ (μ F)} {v : PatLensesViews pat ls} →
           get pat ls s ↦ v → put pat ls s v ↦ s
  GetPut pat ls (deconstruct↦ >>= gets↦) = deconstruct↦ >>= GetPuts pat ls gets↦ >>=
                                           return (deconstruct-construct-inverse pat _ deconstruct↦)

open SourceUpdateLens

source-update-lens : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → (⟦ G ⟧ (μ F) ⇆ PatLensesViews pat ls)
source-update-lens pat ls = record { put = put pat ls; get = get pat ls; PutGet = PutGet pat ls; GetPut = GetPut pat ls }
