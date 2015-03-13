module DynamicallyChecked.ListAlignment where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Level
open import Function
open import Data.Bool
import Data.Maybe as Maybe; open Maybe
import Data.Product as Product; open Product
open import Data.List
open import Relation.Binary.PropositionalEquality


filterᴾ : {A : Set} → (A → Par Bool) → List A → Par (List A × List (Maybe A))
filterᴾ p []       = return ([] , [])
filterᴾ p (x ∷ xs) = p x >>= λ b → liftM (if b then Product.map (_∷_ x) (_∷_ nothing)
                                               else Product.map id      (_∷_ (just x)))
                                         (filterᴾ p xs)

AllTrueᴾ : {A : Set} → (A → Par Bool) → List A → Set₁
AllTrueᴾ p [] = ⊤
AllTrueᴾ p (x ∷ xs) = (p x ↦ true) × AllTrueᴾ p xs

AllFalseᴾ : {A : Set} → (A → Par Bool) → List A → Set₁
AllFalseᴾ p []       = ⊤
AllFalseᴾ p (x ∷ xs) = (p x ↦ false) × AllFalseᴾ p xs

AllFalseᴾᴹ : {A : Set} → (A → Par Bool) → List (Maybe A) → Set₁
AllFalseᴾᴹ p [] = ⊤
AllFalseᴾᴹ p (nothing ∷ mxs) = AllFalseᴾᴹ p mxs
AllFalseᴾᴹ p (just x  ∷ mxs) = (p x ↦ false) × AllFalseᴾᴹ p mxs

filterᴾ-all-true : {A : Set} {p : A → Par Bool} {xs xs' : List A} {rs : List (Maybe A)} →
                   filterᴾ p xs ↦ (xs' , rs) → AllTrueᴾ p xs'
filterᴾ-all-true {xs = []    } (return refl) = tt
filterᴾ-all-true {xs = x ∷ xs} (_>>=_ {x = true } p-x↦true  (filterᴾ-comp >>= return refl)) =
  p-x↦true , filterᴾ-all-true filterᴾ-comp
filterᴾ-all-true {xs = x ∷ xs} (_>>=_ {x = false} p-x↦false (filterᴾ-comp >>= return refl)) =
 filterᴾ-all-true filterᴾ-comp

filterᴾ-all-false : {A : Set} {p : A → Par Bool} {xs xs' : List A} {rs : List (Maybe A)} →
                    filterᴾ p xs ↦ (xs' , rs) → AllFalseᴾᴹ p rs
filterᴾ-all-false {xs = []    } (return refl) = tt
filterᴾ-all-false {xs = x ∷ xs} (_>>=_ {x = true } p-x↦true  (filterᴾ-comp >>= return refl)) =
  filterᴾ-all-false filterᴾ-comp
filterᴾ-all-false {xs = x ∷ xs} (_>>=_ {x = false} p-x↦false (filterᴾ-comp >>= return refl)) =
  p-x↦false , filterᴾ-all-false filterᴾ-comp

condense : {A : Set} → List (Maybe A) → List A
condense []              = []
condense (nothing ∷ mxs) = condense mxs
condense (just x  ∷ mxs) = x ∷ condense mxs

invert-filterᴾ : {A : Set} → List A → List (Maybe A) → List A
invert-filterᴾ xs       []              = xs
invert-filterᴾ []       (my      ∷ mys) = condense (my ∷ mys)
invert-filterᴾ (x ∷ xs) (nothing ∷ mys) = x ∷ invert-filterᴾ xs mys
invert-filterᴾ (x ∷ xs) (just y  ∷ mys) = y ∷ invert-filterᴾ (x ∷ xs) mys

condense-inverse : {A : Set} (p : A → Par Bool) (xs : List A) {mys : List (Maybe A)} →
                   filterᴾ p xs ↦ ([] , mys) → condense mys ≡ xs
condense-inverse p []       (return refl) = refl
condense-inverse p (x ∷ xs) (_>>=_ {x = true } p-x↦true  (filterᴾ-comp >>= return ()  ))
condense-inverse p (x ∷ xs) (_>>=_ {x = false} p-x↦false (filterᴾ-comp >>= return refl)) =
  cong (_∷_ x) (condense-inverse p xs filterᴾ-comp)

filterᴾ-inverse : {A : Set} (p : A → Par Bool) (xs : List A) {xs' : List A} {mys : List (Maybe A)} →
                      filterᴾ p xs ↦ (xs' , mys) → invert-filterᴾ xs' mys ≡ xs
filterᴾ-inverse p []       (return refl) = refl
filterᴾ-inverse p (x ∷ xs) (_>>=_ {x = true } p-x↦true  (filterᴾ-comp >>= return refl)) =
  cong (_∷_ x) (filterᴾ-inverse p xs filterᴾ-comp)
filterᴾ-inverse p (x ∷ xs) (_>>=_ {x = false} p-x↦false (_>>=_ {x = []       , mys} filterᴾ-comp (return refl))) =
  cong (_∷_ x) (condense-inverse p xs filterᴾ-comp)
filterᴾ-inverse p (x ∷ xs) (_>>=_ {x = false} p-x↦false (_>>=_ {x = x' ∷ xs' , mys} filterᴾ-comp (return refl))) =
  cong (_∷_ x) (filterᴾ-inverse p xs filterᴾ-comp)

filterᴾ-condense-inverse :
  {A : Set} {p : A → Par Bool} (mys : List (Maybe A)) →
  AllFalseᴾᴹ p mys → Σ[ mws' ∈ List (Maybe A) ] (filterᴾ p (condense mys) ↦ ([] , mws'))
filterᴾ-condense-inverse []         all = , return refl
filterᴾ-condense-inverse (nothing ∷ mys) all = filterᴾ-condense-inverse mys all
filterᴾ-condense-inverse (just y  ∷ mys) all = , (proj₁ all >>= proj₂ (filterᴾ-condense-inverse mys (proj₂ all)) >>= return refl)

filterᴾ-invert-inverse :
  {A : Set} {p : A → Par Bool} {xs zs : List A} {mys mws : List (Maybe A)} →
  AllFalseᴾᴹ p mys → filterᴾ p xs ↦ (zs , mws) → Σ[ mws' ∈ List (Maybe A) ] (filterᴾ p (invert-filterᴾ xs mys) ↦ (zs , mws'))
filterᴾ-invert-inverse {xs = xs    } {mys = []           } all filterᴾ-comp  = , filterᴾ-comp
filterᴾ-invert-inverse {xs = []    } {mys = my      ∷ mys} all (return refl) = filterᴾ-condense-inverse (my ∷ mys) all
filterᴾ-invert-inverse {xs = x ∷ xs} {mys = nothing ∷ mys} all (_>>=_ {x = true } p-x↦true  (filterᴾ-comp >>= return refl)) =
  , (p-x↦true >>= proj₂ (filterᴾ-invert-inverse {mys = mys} all filterᴾ-comp) >>= return refl)
filterᴾ-invert-inverse {xs = x ∷ xs} {mys = nothing ∷ mys} all (_>>=_ {x = false} p-x↦false (filterᴾ-comp >>= return refl)) =
  , (p-x↦false >>= proj₂ (filterᴾ-invert-inverse {mys = mys} all filterᴾ-comp) >>= return refl)
filterᴾ-invert-inverse {xs = x ∷ xs} {mys = just y  ∷ mys} all filterᴾ-comp =
  _ , (proj₁ all >>= proj₂ (filterᴾ-invert-inverse {mys = mys} (proj₂ all) filterᴾ-comp) >>= return refl)

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

  align : List V → List S → Par (List S × List S)  -- returns unmatched sources and aligned sources
  align []       ss       = liftM (flip _,_ []) (concealSs ss)
  align (v ∷ vs) []       = liftM (_,_ []) (createSs (v ∷ vs))
  align (v ∷ vs) (s ∷ ss) = firstMatch v (s ∷ ss) >>=
                              maybe (λ { (s' , ss') → syncSV s' v >>= λ s'' → liftM (Product.map id (_∷_ s'')) (align vs ss') })
                                    (liftM₂ (λ s' → Product.map id (_∷_ s')) (createS v) (align vs (s ∷ ss)))

  put : List S → List V → Par (List S)
  put ss vs = filterᴾ sourceCondition ss >>= λ { (filtered , residual) →
              align vs filtered >>= λ { (concealed , synced) →
              return (invert-filterᴾ (concealed ++ synced) residual) } }
  
  getV : S → Par V
  getV s = Lens.get elem-lens s >>= λ v → match? s v >>= λ b → assert b then return v

  get : List S → Par (List V)
  get = mapPar getV ∘ proj₁ <=< filterᴾ sourceCondition

  PutGet-createSs : (vs : List V) {ss : List S} → createSs vs ↦ ss → get ss ↦ vs
  PutGet-createSs []       (return refl) = return refl >>= return refl
  PutGet-createSs (v ∷ vs) ((create-v↦s >>= put-s-v↦s' >>= match?-s-v↦true >>= assert refl then sourceCondition-s'↦true >>= assert refl then return refl) >>= createSs-vs↦ss' >>= return refl) with PutGet-createSs vs
  PutGet-createSs (v ∷ vs) ((create-v↦s >>= put-s-v↦s' >>= match?-s-v↦true >>= assert refl then sourceCondition-s'↦true >>= assert refl then return refl) >>= createSs-vs↦ss' >>= return refl) | comp =
  (sourceCondition-s'↦true >>= {!!} >>= return refl) >>= (Lens.PutGet elem-lens put-s-v↦s' >>= match?-s-v↦true >>= assert refl then return refl) >>= {!!} >>= return refl

  PutGet-align : (vs : List V) (ss : List S) {unmatched aligned : List S} →
                 align vs ss ↦ (unmatched , aligned) → get aligned ↦ vs
  PutGet-align []       ss       (_ >>= return refl)    = return refl >>= return refl
  PutGet-align (v ∷ vs) []       (comp >>= return refl) = PutGet-createSs (v ∷ vs) comp
  PutGet-align (v ∷ vs) (s ∷ ss) comp                   = {!!}

  PutGet : {ss : List S} {vs : List V} {ss' : List S} → put ss vs ↦ ss' → get ss' ↦ vs
  PutGet (_>>=_ {x = (filtered , residuals)} filterᴾ-comp (_>>=_ {x = (unmatched , aligned)} align-comp (return refl))) = {!!}

  GetPut-align : (vs : List V) (ss : List S) → AllTrueᴾ sourceCondition ss → mapPar getV ss ↦ vs → align vs ss ↦ ([] , ss)
  GetPut-align []        ss       all comp with mapPar-equals-nil comp
  GetPut-align []       .[]       all comp | refl = return refl >>= return refl
  GetPut-align (v ∷ vs)  []       all (return ())
  GetPut-align (v ∷ vs)  (s ∷ ss) all ((get-s↦v >>= match?-s-v↦true >>= assert refl then return refl) >>=
                                         mapPar-getV-ss↦vs >>= return refl) =
    (match?-s-v↦true >>= return refl) >>=
    (Lens.GetPut elem-lens get-s↦v >>= match?-s-v↦true >>= assert refl then proj₁ all >>= assert refl then return refl) >>=
    GetPut-align vs ss (proj₂ all) mapPar-getV-ss↦vs >>= return refl

  GetPut : {ss : List S} {vs : List V} → get ss ↦ vs → put ss vs ↦ ss
  GetPut (filterᴾ-comp >>= mapPar-comp) =
    filterᴾ-comp >>=
    GetPut-align _ _ (filterᴾ-all-true filterᴾ-comp) mapPar-comp >>=
    return (filterᴾ-inverse sourceCondition _ filterᴾ-comp)

align-lens : {S V : Set} (sourceCondition : S → Par Bool) (match? : S → V → Par Bool)
             (elem-lens : S ⇆ V) (create : V → Par S) (conceal : S → Par (Maybe S)) → List S ⇆ List V
align-lens sourceCondition match? elem-lens create conceal =
  record { put = put; get = get; PutGet = PutGet; GetPut = GetPut }
  where open AlignLens sourceCondition match? elem-lens create conceal
