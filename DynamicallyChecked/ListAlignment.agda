module DynamicallyChecked.ListAlignment where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Level
open import Function
open import Data.Bool
import Data.Maybe as Maybe; open Maybe
import Data.Product as Product; open Product
open import Data.List
open import Relation.Binary.PropositionalEquality


filterPar : {A : Set} → (A → Par Bool) → List A → Par (List A × List (Maybe A))
filterPar p []       = return ([] , [])
filterPar p (x ∷ xs) = p x >>= λ b → liftM (if b then Product.map (_∷_ x) (_∷_ nothing)
                                                 else Product.map id      (_∷_ (just x)))
                                           (filterPar p xs)

condense : {A : Set} → List (Maybe A) → List A
condense []              = []
condense (nothing ∷ mxs) = condense mxs
condense (just x  ∷ mxs) = x ∷ condense mxs

invert-filterPar : {A : Set} → List A → List (Maybe A) → List A
invert-filterPar xs       []              = xs
invert-filterPar []       (my      ∷ mys) = condense (my ∷ mys)
invert-filterPar (x ∷ xs) (nothing ∷ mys) = x ∷ invert-filterPar xs mys
invert-filterPar (x ∷ xs) (just y  ∷ mys) = y ∷ invert-filterPar (x ∷ xs) mys

condense-inverse : {A : Set} (p : A → Par Bool) (xs : List A) {mys : List (Maybe A)} →
                   filterPar p xs ↦ ([] , mys) → condense mys ≡ xs
condense-inverse p []       (return refl) = refl
condense-inverse p (x ∷ xs) (_>>=_ {x = true } p-x↦true  (filterPar-comp >>= return ()  ))
condense-inverse p (x ∷ xs) (_>>=_ {x = false} p-x↦false (filterPar-comp >>= return refl)) =
  cong (_∷_ x) (condense-inverse p xs filterPar-comp)

filterPar-inverse : {A : Set} (p : A → Par Bool) (xs : List A) {xs' : List A} {mys : List (Maybe A)} →
                      filterPar p xs ↦ (xs' , mys) → invert-filterPar xs' mys ≡ xs
filterPar-inverse p []       (return refl) = refl
filterPar-inverse p (x ∷ xs) (_>>=_ {x = true } p-x↦true  (filterPar-comp >>= return refl)) =
  cong (_∷_ x) (filterPar-inverse p xs filterPar-comp)
filterPar-inverse p (x ∷ xs) (_>>=_ {x = false} p-x↦false (_>>=_ {x = []       , mys} filterPar-comp (return refl))) =
  cong (_∷_ x) (condense-inverse p xs filterPar-comp)
filterPar-inverse p (x ∷ xs) (_>>=_ {x = false} p-x↦false (_>>=_ {x = x' ∷ xs' , mys} filterPar-comp (return refl))) =
  cong (_∷_ x) (filterPar-inverse p xs filterPar-comp)

mapPar : {A B : Set} → (A → Par B) → List A → Par (List B)
mapPar f []       = return []
mapPar f (x ∷ xs) = liftM₂ _∷_ (f x) (mapPar f xs)

mapPar-equals-nil : {A B : Set} {f : A → Par B} {xs : List A} → mapPar f xs ↦ [] → xs ≡ []
mapPar-equals-nil {xs = []    } comp = refl
mapPar-equals-nil {xs = x ∷ xs} (_ >>= _ >>= return ())

foldrPar : {A B : Set} → (A → B → Par B) → B → List A → Par B
foldrPar f e []       = return e
foldrPar f e (x ∷ xs) = foldrPar f e xs >>= f x

module AlignLens {S V : Set} (sourceCondition : S → Par Bool) (match? : S → V → Par Bool)
                 (elem-lens : S ⇆ V) (create : V → Par S) (conceal : S → Par (Maybe S)) where

  -- data MatchWith : List V → List S → Set where
  --   nil  : {ss : List S} → MatchWith [] ss
  --   cons : {v : V} {vs : List V} {s : S} {ss : List S} →
  --          match? s v ≡ᴶ true → MatchWith vs ss → MatchWith (v ∷ vs) (s ∷ ss)

  syncSV : S → V → Par S
  syncSV s v = Lens.put elem-lens s v >>= λ s' →
               match? s' v >>= λ matched →
               assert matched then
               sourceCondition s' >>= λ revealed →
               assert revealed then
               return s'

  createS : V → Par S
  createS v = create v >>= λ s → syncSV s v

  createSs : List V → Par (List S)
  createSs []       = return []
  createSs (v ∷ vs) = liftM₂ _∷_ (createS v) (createSs vs)

  firstMatch : V → List S → Par (Maybe (S × List S))
  firstMatch v []       = return nothing
  firstMatch v (s ∷ ss) = match? s v >>= λ b → if b then return (just (s , ss))
                                                    else liftM (Maybe.map (Product.map id (_∷_ s))) (firstMatch v ss)

  concealSs : List S → Par (List S)
  concealSs = foldrPar (λ s ss' → conceal s >>=
                                    maybe (λ s' → sourceCondition s' >>= λ b → assert (not b) then return (s' ∷ ss'))
                                          (return ss')) []

  align : List V → List S → Par (List S × List S)
  align []       ss       = liftM (flip _,_ []) (concealSs ss)
  align (v ∷ vs) []       = liftM (_,_ []) (createSs (v ∷ vs))
  align (v ∷ vs) (s ∷ ss) = firstMatch v (s ∷ ss) >>=
                              maybe (λ { (s' , ss') → liftM (Product.map id (_∷_ s')) (align vs ss') })
                                    (liftM₂ (λ s' → Product.map id (_∷_ s')) (createS v) (align vs (s ∷ ss)))

  put : List S → List V → Par (List S)
  put ss vs = filterPar sourceCondition ss >>= λ { (filtered , residual) →
              align vs filtered >>= λ { (synced , concealed) →
              return (invert-filterPar (synced ++ concealed) residual) } }
  
  getV : S → Par V
  getV s = Lens.get elem-lens s >>= λ v → match? s v >>= λ b → assert b then return v

  get : List S → Par (List V)
  get = mapPar getV ∘ proj₁ <=< filterPar sourceCondition

  GetPut-align : (vs : List V) (ss : List S) → mapPar getV ss ↦ vs → align vs ss ↦ ([] , ss)
  GetPut-align []        ss       comp with mapPar-equals-nil comp
  GetPut-align []       .[]       comp | refl = return refl >>= return refl
  GetPut-align (v ∷ vs)  []       (return ())
  GetPut-align (v ∷ vs)  (s ∷ ss) ((get-s↦v >>= match?-s-v↦true >>= assert refl then return refl) >>=
                                     mapPar-getV-ss↦vs >>= return refl) =
    (match?-s-v↦true >>= return refl) >>= GetPut-align vs ss mapPar-getV-ss↦vs >>= return refl

  GetPut : {ss : List S} {vs : List V} → get ss ↦ vs → put ss vs ↦ ss
  GetPut (filterPar-comp >>= mapPar-comp) =
    filterPar-comp >>= GetPut-align _ _ mapPar-comp >>= return (filterPar-inverse sourceCondition _ filterPar-comp)
