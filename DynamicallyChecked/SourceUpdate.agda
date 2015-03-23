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


mutual

  PatLenses :  {G : U n} → Pattern F G → Set₁
  PatLenses {G} var              = Σ[ V ∈ Set ] (⟦ G ⟧ (μ F) ⇆ V)
  PatLenses     (const x       ) = ⊤
  PatLenses     (child pat     ) = PatLenses pat
  PatLenses     (left pat      ) = PatLenses pat
  PatLenses     (right pat     ) = PatLenses pat
  PatLenses     (prod lpat rpat) = PatLenses lpat × PatLenses rpat
  PatLenses     (list pats     ) = PatLenses-list pats

  PatLenses-list : {G : U n} → List (Pattern F G) → Set₁
  PatLenses-list {G} []           = Σ[ V ∈ Set ] (List (⟦ G ⟧ (μ F)) ⇆ V)
  PatLenses-list     (pat ∷ pats) = PatLenses pat × PatLenses-list pats

mutual

  PatLensesViews : {G : U n} (pat : Pattern F G) → PatLenses pat → Set
  PatLensesViews var              (V , _)    = V
  PatLensesViews (const x       ) tt         = ⊤
  PatLensesViews (child pat     ) ls         = PatLensesViews pat ls
  PatLensesViews (left pat      ) ls         = PatLensesViews pat ls
  PatLensesViews (right pat     ) ls         = PatLensesViews pat ls
  PatLensesViews (prod lpat rpat) (ls , ls') = PatLensesViews lpat ls × PatLensesViews rpat ls'
  PatLensesViews (list pats     ) ls         = PatLensesViews-list pats ls

  PatLensesViews-list : {G : U n} (pats : List (Pattern F G)) → PatLenses-list pats → Set
  PatLensesViews-list []           (V , _)    = V
  PatLensesViews-list (pat ∷ pats) (ls , ls') = PatLensesViews pat ls × PatLensesViews-list pats ls'

module SourceUpdateLens where

  mutual

    puts : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → ⟦ pat ⟧ᴾ → PatLensesViews pat ls → Par ⟦ pat ⟧ᴾ
    puts     var              (V , l)     s        v       = Lens.put l s v
    puts {G} (const x       ) ls          tt       v       = return tt
    puts     (child pat     ) ls          s        v       = puts pat ls s v
    puts     (left pat      ) ls          s        v       = puts pat ls s v
    puts     (right pat     ) ls          s        v       = puts pat ls s v
    puts     (prod lpat rpat) (ls , ls') (s , s') (v , v') = liftPar₂ _,_ (puts lpat ls s v) (puts rpat ls' s' v')
    puts     (list pats     ) ls          s        v       = puts-list pats ls s v

    puts-list : {G : U n} (pats : List (Pattern F G)) (ls : PatLenses-list pats) →
                ⟦ pats ⟧ᴾᴸ → PatLensesViews-list pats ls → Par ⟦ pats ⟧ᴾᴸ
    puts-list []           (V  , l)    s        v       = Lens.put l s v
    puts-list (pat ∷ pats) (ls , ls') (s , s') (v , v') = liftPar₂ _,_ (puts pat ls s v) (puts-list pats ls' s' v')

  put : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → ⟦ G ⟧ (μ F) → PatLensesViews pat ls → Par (⟦ G ⟧ (μ F))
  put pat ls s v = deconstruct pat s >>= λ s' → liftPar (construct pat) (puts pat ls s' v)

  mutual

    gets : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → ⟦ pat ⟧ᴾ → Par (PatLensesViews pat ls)
    gets var              (V , l)     s       = Lens.get l s
    gets (const x       ) ls          tt      = return tt
    gets (child pat     ) ls          s       = gets pat ls s
    gets (left pat      ) ls          s       = gets pat ls s
    gets (right pat     ) ls          s       = gets pat ls s
    gets (prod lpat rpat) (ls , ls') (s , s') = liftPar₂ _,_ (gets lpat ls s) (gets rpat ls' s')
    gets (list pats     ) ls          s       = gets-list pats ls s

    gets-list : {G : U n} (pats : List (Pattern F G)) (ls : PatLenses-list pats) → ⟦ pats ⟧ᴾᴸ → Par (PatLensesViews-list pats ls)
    gets-list []           (V , l)    s        = Lens.get l s
    gets-list (pat ∷ pats) (ls , ls') (s , s') = liftPar₂ _,_ (gets pat ls s) (gets-list pats ls' s')

  get : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → ⟦ G ⟧ (μ F) → Par (PatLensesViews pat ls)
  get pat ls = gets pat ls  <=< deconstruct pat

  mutual

    PutGets : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) {s : ⟦ pat ⟧ᴾ} {v : PatLensesViews pat ls} {s' : ⟦ pat ⟧ᴾ} →
              puts pat ls s v ↦ s' → gets pat ls s' ↦ v
    PutGets var              (V , l)    put↦  = Lens.PutGet l put↦
    PutGets (const x       ) ls         puts↦ = return refl
    PutGets (child pat     ) ls         puts↦ = PutGets pat ls puts↦
    PutGets (left pat      ) ls         puts↦ = PutGets pat ls puts↦
    PutGets (right pat     ) ls         puts↦ = PutGets pat ls puts↦
    PutGets (prod lpat rpat) (ls , ls') (lputs↦ >>= rputs↦ >>= return refl) =
      PutGets lpat ls lputs↦ >>= PutGets rpat ls' rputs↦ >>= return refl
    PutGets (list pats     ) ls         puts↦ = PutGets-list pats ls puts↦

    PutGets-list : {G : U n} (pats : List (Pattern F G)) (ls : PatLenses-list pats)
                   {s : ⟦ pats ⟧ᴾᴸ} {v : PatLensesViews-list pats ls} {s' : ⟦ pats ⟧ᴾᴸ} →
                   puts-list pats ls s v ↦ s' → gets-list pats ls s' ↦ v
    PutGets-list []           (V , l)    put↦ = Lens.PutGet l put↦
    PutGets-list (pat ∷ pats) (ls , ls') (puts↦ >>= puts-list↦ >>= return refl) =
      PutGets pat ls puts↦ >>= PutGets-list pats ls' puts-list↦ >>= return refl

  PutGet : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) {s : ⟦ G ⟧ (μ F)} {v : PatLensesViews pat ls} {s' : ⟦ G ⟧ (μ F)} →
           put pat ls s v ↦ s' → get pat ls s' ↦ v
  PutGet pat ls (deconstruct↦ >>= puts↦ >>= return refl) = construct-deconstruct-inverse pat _ >>= PutGets pat ls puts↦

  mutual

    GetPuts : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) {s : ⟦ pat ⟧ᴾ} {v : PatLensesViews pat ls} →
              gets pat ls s ↦ v → puts pat ls s v ↦ s
    GetPuts var              (V , l)    get↦  = Lens.GetPut l get↦
    GetPuts (const x       ) ls         gets↦ = return refl
    GetPuts (child pat     ) ls         gets↦ = GetPuts pat ls gets↦
    GetPuts (left pat      ) ls         gets↦ = GetPuts pat ls gets↦
    GetPuts (right pat     ) ls         gets↦ = GetPuts pat ls gets↦
    GetPuts (prod lpat rpat) (ls , ls') (lgets↦ >>= rgets↦ >>= return refl) =
      GetPuts lpat ls lgets↦ >>= GetPuts rpat ls' rgets↦ >>= return refl
    GetPuts (list pats     ) ls         gets↦ = GetPuts-list pats ls gets↦

    GetPuts-list : {G : U n} (pats : List (Pattern F G)) (ls : PatLenses-list pats)
                   {s : ⟦ pats ⟧ᴾᴸ} {v : PatLensesViews-list pats ls} →
                   gets-list pats ls s ↦ v → puts-list pats ls s v ↦ s
    GetPuts-list []           (V , l)    get↦ = Lens.GetPut l get↦
    GetPuts-list (pat ∷ pats) (ls , ls') (gets↦ >>= gets-list↦ >>= return refl) =
      GetPuts pat ls gets↦ >>= GetPuts-list pats ls' gets-list↦ >>= return refl

  GetPut : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) {s : ⟦ G ⟧ (μ F)} {v : PatLensesViews pat ls} →
           get pat ls s ↦ v → put pat ls s v ↦ s
  GetPut pat ls (deconstruct↦ >>= gets↦) = deconstruct↦ >>= GetPuts pat ls gets↦ >>=
                                           return (deconstruct-construct-inverse pat _ deconstruct↦)

open SourceUpdateLens

source-update-lens : {G : U n} (pat : Pattern F G) (ls : PatLenses pat) → (⟦ G ⟧ (μ F) ⇆ PatLensesViews pat ls)
source-update-lens pat ls = record { put = put pat ls; get = get pat ls; PutGet = PutGet pat ls; GetPut = GetPut pat ls }
