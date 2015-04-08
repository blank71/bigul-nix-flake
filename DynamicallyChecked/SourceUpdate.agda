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

  put : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → PatResult pat → PatLensesViews pat ls → Par (PatResult pat)
  put     var              (V , l)     s        v       = Lens.put l s v
  put {G} (k x           ) ls          tt       v       = return tt
  put     (child pat     ) ls          s        v       = put pat ls s v
  put     (left pat      ) ls          s        v       = put pat ls s v
  put     (right pat     ) ls          s        v       = put pat ls s v
  put     (prod lpat rpat) (ls , ls') (s , s') (v , v') = liftPar₂ _,_ (put lpat ls s v) (put rpat ls' s' v')
  put     (elem hpat tpat) (ls , ls') (s , s') (v , v') = liftPar₂ _,_ (put hpat ls s v) (put tpat ls' s' v')

  get : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → PatResult pat → Par (PatLensesViews pat ls)
  get var              (V , l)     s       = Lens.get l s
  get (k x           ) ls          tt      = return tt
  get (child pat     ) ls          s       = get pat ls s
  get (left pat      ) ls          s       = get pat ls s
  get (right pat     ) ls          s       = get pat ls s
  get (prod lpat rpat) (ls , ls') (s , s') = liftPar₂ _,_ (get lpat ls s) (get rpat ls' s')
  get (elem hpat tpat) (ls , ls') (s , s') = liftPar₂ _,_ (get hpat ls s) (get tpat ls' s')

  PutGet : {G : U n} (pat : Pattern F G) (ls : PatLenses pat)
           {s : PatResult pat} {v : PatLensesViews pat ls} {s' : PatResult pat} →
           put pat ls s v ↦ s' → get pat ls s' ↦ v
  PutGet var              (V , l)    put↦  = Lens.PutGet l put↦
  PutGet (k x           ) ls         put↦ = return refl
  PutGet (child pat     ) ls         put↦ = PutGet pat ls put↦
  PutGet (left pat      ) ls         put↦ = PutGet pat ls put↦
  PutGet (right pat     ) ls         put↦ = PutGet pat ls put↦
  PutGet (prod lpat rpat) (ls , ls') (lput↦ >>= rput↦ >>= return refl) = PutGet lpat ls  lput↦ >>=
                                                                         PutGet rpat ls' rput↦ >>= return refl
  PutGet (elem hpat tpat) (ls , ls') (eput↦ >>= tput↦ >>= return refl) = PutGet hpat ls  eput↦ >>=
                                                                         PutGet tpat ls' tput↦ >>= return refl

  GetPut : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) {s : PatResult pat} {v : PatLensesViews pat ls} →
           get pat ls s ↦ v → put pat ls s v ↦ s
  GetPut var              (V , l)    get↦  = Lens.GetPut l get↦
  GetPut (k x           ) ls         get↦ = return refl
  GetPut (child pat     ) ls         get↦ = GetPut pat ls get↦
  GetPut (left pat      ) ls         get↦ = GetPut pat ls get↦
  GetPut (right pat     ) ls         get↦ = GetPut pat ls get↦
  GetPut (prod lpat rpat) (ls , ls') (lget↦ >>= rget↦ >>= return refl) =
    GetPut lpat ls lget↦ >>= GetPut rpat ls' rget↦ >>= return refl
  GetPut (elem hpat tpat) (ls , ls') (eget↦ >>= tget↦ >>= return refl) =
    GetPut hpat ls eget↦ >>= GetPut tpat ls' tget↦ >>= return refl

open SourceUpdateLens

source-update-lens : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → (PatResult pat ⇆ PatLensesViews pat ls)
source-update-lens pat ls = record { put = put pat ls; get = get pat ls; PutGet = PutGet pat ls; GetPut = GetPut pat ls }
