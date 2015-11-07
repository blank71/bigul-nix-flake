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
filterᴾ p (x ∷ xs) = p x >>= λ b → liftPar (if b then Product.map (_∷_ x) (_∷_ nothing)
                                                 else Product.map id      (_∷_ (just x)))
                                           (filterᴾ p xs)

AllTrueᴾ : {A : Set} → (A → Par Bool) → List A → Set₁
AllTrueᴾ p []       = ⊤
AllTrueᴾ p (x ∷ xs) = (p x ↦ true) × AllTrueᴾ p xs

AllFalseᴾ : {A : Set} → (A → Par Bool) → List A → Set₁
AllFalseᴾ p []       = ⊤
AllFalseᴾ p (x ∷ xs) = (p x ↦ false) × AllFalseᴾ p xs

AllFalseᴾᴹ : {A : Set} → (A → Par Bool) → List (Maybe A) → Set₁
AllFalseᴾᴹ p []              = ⊤
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

filterᴾ-filtered : {A : Set} {p : A → Par Bool} {xs : List A} →
                   AllTrueᴾ p xs → Σ[ mys ∈ List (Maybe A) ] (filterᴾ p xs ↦ (xs , mys))
filterᴾ-filtered {xs = []    } all = , return refl
filterᴾ-filtered {xs = x ∷ xs} all = , (proj₁ all >>= proj₂ (filterᴾ-filtered (proj₂ all)) >>= return refl)

filterᴾ-append-residual :
  {A : Set} {p : A → Par Bool} {xs ys zs : List A} {mws : List (Maybe A)} →
  AllFalseᴾ p xs → filterᴾ p ys ↦ (zs , mws) → Σ[ mws' ∈ List (Maybe A) ] (filterᴾ p (xs ++ ys) ↦ (zs , mws'))
filterᴾ-append-residual {xs = []    } all comp = , comp
filterᴾ-append-residual {xs = x ∷ xs} all comp =
  , (proj₁ all >>= proj₂ (filterᴾ-append-residual (proj₂ all) comp) >>= return refl)

condense : {A : Set} → List (Maybe A) → List A
condense []              = []
condense (nothing ∷ mxs) = condense mxs
condense (just x  ∷ mxs) = x ∷ condense mxs

unfilterᴾ : {A : Set} → List A → List (Maybe A) → List A
unfilterᴾ xs       []              = xs
unfilterᴾ []       (my      ∷ mys) = condense (my ∷ mys)
unfilterᴾ (x ∷ xs) (nothing ∷ mys) = x ∷ unfilterᴾ xs mys
unfilterᴾ (x ∷ xs) (just y  ∷ mys) = y ∷ unfilterᴾ (x ∷ xs) mys

filterᴾ-condense-inverse : {A : Set} (p : A → Par Bool) (xs : List A) {mys : List (Maybe A)} →
                           filterᴾ p xs ↦ ([] , mys) → condense mys ≡ xs
filterᴾ-condense-inverse p []       (return refl) = refl
filterᴾ-condense-inverse p (x ∷ xs) (_>>=_ {x = true } p-x↦true  (filterᴾ-comp >>= return ()  ))
filterᴾ-condense-inverse p (x ∷ xs) (_>>=_ {x = false} p-x↦false (filterᴾ-comp >>= return refl)) =
  cong (_∷_ x) (filterᴾ-condense-inverse p xs filterᴾ-comp)

filterᴾ-unfilterᴾ-inverse : {A : Set} (p : A → Par Bool) (xs : List A) {xs' : List A} {mys : List (Maybe A)} →
                            filterᴾ p xs ↦ (xs' , mys) → unfilterᴾ xs' mys ≡ xs
filterᴾ-unfilterᴾ-inverse p []       (return refl) = refl
filterᴾ-unfilterᴾ-inverse p (x ∷ xs) (_>>=_ {x = true } p-x↦true  (filterᴾ-comp >>= return refl)) =
  cong (_∷_ x) (filterᴾ-unfilterᴾ-inverse p xs filterᴾ-comp)
filterᴾ-unfilterᴾ-inverse p (x ∷ xs)
  (_>>=_ {x = false} p-x↦false (_>>=_ {x = []       , mys} filterᴾ-comp (return refl))) =
  cong (_∷_ x) (filterᴾ-condense-inverse p xs filterᴾ-comp)
filterᴾ-unfilterᴾ-inverse p (x ∷ xs)
  (_>>=_ {x = false} p-x↦false (_>>=_ {x = x' ∷ xs' , mys} filterᴾ-comp (return refl))) =
  cong (_∷_ x) (filterᴾ-unfilterᴾ-inverse p xs filterᴾ-comp)

condense-filterᴾ-inverse : {A : Set} {p : A → Par Bool} (mys : List (Maybe A)) →
                           AllFalseᴾᴹ p mys → Σ[ mws' ∈ List (Maybe A) ] (filterᴾ p (condense mys) ↦ ([] , mws'))
condense-filterᴾ-inverse []              all = , return refl
condense-filterᴾ-inverse (nothing ∷ mys) all = condense-filterᴾ-inverse mys all
condense-filterᴾ-inverse (just y  ∷ mys) all =
  , (proj₁ all >>= proj₂ (condense-filterᴾ-inverse mys (proj₂ all)) >>= return refl)

unfilterᴾ-filterᴾ-inverse : {A : Set} {p : A → Par Bool} {xs zs : List A} {mys mws : List (Maybe A)} →
                            AllFalseᴾᴹ p mys → filterᴾ p xs ↦ (zs , mws) →
                            Σ[ mws' ∈ List (Maybe A) ] (filterᴾ p (unfilterᴾ xs mys) ↦ (zs , mws'))
unfilterᴾ-filterᴾ-inverse {xs = xs    } {mys = []           } all filterᴾ-comp  = , filterᴾ-comp
unfilterᴾ-filterᴾ-inverse {xs = []    } {mys = my      ∷ mys} all (return refl) = condense-filterᴾ-inverse (my ∷ mys) all
unfilterᴾ-filterᴾ-inverse {xs = x ∷ xs} {mys = nothing ∷ mys} all
  (_>>=_ {x = true } p-x↦true  (filterᴾ-comp >>= return refl)) =
  , (p-x↦true >>= proj₂ (unfilterᴾ-filterᴾ-inverse {mys = mys} all filterᴾ-comp) >>= return refl)
unfilterᴾ-filterᴾ-inverse {xs = x ∷ xs} {mys = nothing ∷ mys} all
  (_>>=_ {x = false} p-x↦false (filterᴾ-comp >>= return refl)) =
  , (p-x↦false >>= proj₂ (unfilterᴾ-filterᴾ-inverse {mys = mys} all filterᴾ-comp) >>= return refl)
unfilterᴾ-filterᴾ-inverse {xs = x ∷ xs} {mys = just y  ∷ mys} all filterᴾ-comp =
  , (proj₁ all >>= proj₂ (unfilterᴾ-filterᴾ-inverse {mys = mys} (proj₂ all) filterᴾ-comp) >>= return refl)

module AlignLens {S V : Set} (source-condition : S → Par Bool) (match? : S → V → Par Bool)
                 (elem-lens : S ⇆ V) (create : V → Par S) (conceal : S → Par (Maybe S)) where

  put-and-check : S → V → Par S
  put-and-check s v = Lens.put elem-lens s v >>= λ s' →
                       match? s' v >>= λ matched →
                       assert matched then
                       source-condition s' >>= λ revealed →
                       assert revealed then
                       return s'

  put-and-check-true : {s : S} {v : V} {s' : S} → put-and-check s v ↦ s' → source-condition s' ↦ true
  put-and-check-true (_ >>= _ >>= assert _ then source-condition↦ >>= assert refl then return refl) = source-condition↦

  create-and-check : V → Par S
  create-and-check v = create v >>= λ s → put-and-check s v

  create-and-check-true : {v : V} {s : S} → create-and-check v ↦ s → source-condition s ↦ true
  create-and-check-true (_ >>= source-condition↦) = put-and-check-true source-condition↦

  create-source-list : List V → Par (List S)
  create-source-list []       = return []
  create-source-list (v ∷ vs) = liftPar₂ _∷_ (create-and-check v) (create-source-list vs)

  create-source-list-all-true : {vs : List V} {ss : List S} → create-source-list vs ↦ ss → AllTrueᴾ source-condition ss
  create-source-list-all-true {[]    } (return refl) = tt
  create-source-list-all-true {v ∷ vs} (create-and-check↦ >>= create-source-list↦ >>= return refl) =
    create-and-check-true create-and-check↦ , create-source-list-all-true create-source-list↦

  first-match : V → List S → Par (Maybe (S × List S))
  first-match v []       = return nothing
  first-match v (s ∷ ss) = match? s v >>= λ b → if b then return (just (s , ss))
                                                     else liftPar (Maybe.map (Product.map id (_∷_ s))) (first-match v ss)

  conceal-source-list : List S → Par (List S)
  conceal-source-list = foldrPar (λ s ss' → conceal s >>=
                                            maybe (λ s' → source-condition s' >>= λ b →
                                                          assert-not b then return (s' ∷ ss'))
                                                  (return ss')) []

  conceal-source-list-all-false : {ss ss' : List S} → conceal-source-list ss ↦ ss' → AllFalseᴾ source-condition ss'
  conceal-source-list-all-false {[]    } (return refl) = tt
  conceal-source-list-all-false {s ∷ ss} (conceal-source-list↦ >>= (_>>=_ {x = just s'} conceal↦ (source-condition↦ >>= assert-not refl then return refl))) =
    source-condition↦ , conceal-source-list-all-false conceal-source-list↦
  conceal-source-list-all-false {s ∷ ss} (conceal-source-list↦ >>= (_>>=_ {x = nothing} conceal↦ (return refl))) =
    conceal-source-list-all-false conceal-source-list↦

  align : List V → List S → Par (List S × List S)  -- returns unmatched sources and aligned sources
  align []       ss       = liftPar (flip _,_ []) (conceal-source-list ss)
  align (v ∷ vs) []       = liftPar (_,_ []) (create-source-list (v ∷ vs))
  align (v ∷ vs) (s ∷ ss) = first-match v (s ∷ ss) >>=
                            maybe (λ { (s' , ss') → put-and-check s' v >>= λ s'' →
                                                    liftPar (Product.map id (_∷_ s'')) (align vs ss') })
                                  (liftPar₂ (λ s' → Product.map id (_∷_ s')) (create-and-check v) (align vs (s ∷ ss)))

  align-all-true : (vs : List V) (ss : List S) {unmatched aligned : List S} →
                   align vs ss ↦ (unmatched , aligned) → AllTrueᴾ source-condition aligned
  align-all-true []       ss       (_ >>= return refl) = tt
  align-all-true (v ∷ vs) []       (comp >>= return refl) = create-source-list-all-true comp
  align-all-true (v ∷ vs) (s ∷ ss) (_>>=_ {x = just (s' , ss')} first-match↦ (put-and-check↦ >>= align↦ >>= return refl)) =
    put-and-check-true put-and-check↦ , align-all-true vs ss' align↦
  align-all-true (v ∷ vs) (s ∷ ss) (_>>=_ {x = nothing} first-match↦ (create-and-check↦ >>= align↦ >>= return refl)) =
    create-and-check-true create-and-check↦ , align-all-true vs (s ∷ ss) align↦

  align-all-false : (vs : List V) (ss : List S) {unmatched aligned : List S} →
                    align vs ss ↦ (unmatched , aligned) → AllFalseᴾ source-condition unmatched
  align-all-false []       ss       (concealSs↦ >>= return refl) = conceal-source-list-all-false concealSs↦
  align-all-false (v ∷ vs) []       (_ >>= return refl) = tt
  align-all-false (v ∷ vs) (s ∷ ss) (_>>=_ {x = just (s' , ss')} first-match↦ (put-and-check↦ >>= align↦ >>= return refl)) =
    align-all-false vs ss' align↦
  align-all-false (v ∷ vs) (s ∷ ss) (_>>=_ {x = nothing} first-match↦ (create-and-check↦ >>= align↦ >>= return refl)) =
    align-all-false vs (s ∷ ss) align↦

  put : List S → List V → Par (List S)
  put ss vs = filterᴾ source-condition ss >>= λ { (filtered , residual) →
              align vs filtered >>= λ { (concealed , synced) →
              return (unfilterᴾ (concealed ++ synced) residual) } }
  
  get-and-check : S → Par V
  get-and-check s = Lens.get elem-lens s >>= λ v → match? s v >>= λ b → assert b then return v

  get : List S → Par (List V)
  get = mapPar get-and-check ∘ proj₁ <=< filterᴾ source-condition

  PutGet-put-and-check : {s s' : S} {v : V} → put-and-check s v ↦ s' → get-and-check s' ↦ v
  PutGet-put-and-check (put-s-v↦s' >>= match?-s'-v↦true >>=
                        assert refl then source-condition-s'↦true >>= assert refl then return refl) =
    Lens.PutGet elem-lens put-s-v↦s' >>= match?-s'-v↦true >>= assert refl then return refl

  PutGet-create-and-check : {v : V} {s : S} → create-and-check v ↦ s → get-and-check s ↦ v
  PutGet-create-and-check (create↦ >>= put-and-check↦) = PutGet-put-and-check put-and-check↦

  PutGet-create-source-list : (vs : List V) {ss : List S} → create-source-list vs ↦ ss → mapPar get-and-check ss ↦ vs
  PutGet-create-source-list []       (return refl) = return refl
  PutGet-create-source-list (v ∷ vs) (create-and-check↦ >>= create-source-list↦ >>= return refl) =
    PutGet-create-and-check create-and-check↦ >>= PutGet-create-source-list vs create-source-list↦ >>= return refl

  PutGet-align : (vs : List V) (ss : List S) {unmatched aligned : List S} →
                 align vs ss ↦ (unmatched , aligned) → mapPar get-and-check aligned ↦ vs
  PutGet-align []       ss       (_ >>= return refl)    = return refl
  PutGet-align (v ∷ vs) []       (comp >>= return refl) = PutGet-create-source-list (v ∷ vs) comp
  PutGet-align (v ∷ vs) (s ∷ ss) (_>>=_ {x = just (s' , ss')} first-match↦ (put-and-check↦ >>= align↦ >>= return refl)) =
    PutGet-put-and-check put-and-check↦ >>= PutGet-align vs ss' align↦ >>= return refl
  PutGet-align (v ∷ vs) (s ∷ ss) (_>>=_ {x = nothing        } first-match↦ (create-and-check↦ >>= align↦ >>= return refl)) =
    PutGet-create-and-check create-and-check↦ >>= PutGet-align vs (s ∷ ss) align↦ >>= return refl

  PutGet : {ss : List S} {vs : List V} {ss' : List S} → put ss vs ↦ ss' → get ss' ↦ vs
  PutGet {ss} {vs} (_>>=_ {x = (filtered , residual)} filterᴾ↦ (_>>=_ {x = (unmatched , aligned)} align↦ (return refl))) =
    proj₂ (unfilterᴾ-filterᴾ-inverse {mys = residual} (filterᴾ-all-false filterᴾ↦)
      (proj₂ (filterᴾ-append-residual (align-all-false vs filtered align↦)
         (proj₂ (filterᴾ-filtered (align-all-true vs filtered align↦)))))) >>= PutGet-align vs filtered align↦

  GetPut-align : (vs : List V) (ss : List S) →
                 AllTrueᴾ source-condition ss → mapPar get-and-check ss ↦ vs → align vs ss ↦ ([] , ss)
  GetPut-align []        []       all comp = return refl >>= return refl
  GetPut-align []        (_ ∷ _)  all (_ >>= _ >>= return ())
  GetPut-align (v ∷ vs)  []       all (return ())
  GetPut-align (v ∷ vs)  (s ∷ ss) all ((get-s↦v >>= match?-s-v↦true >>= assert refl then return refl) >>=
                                        mapPar-get-and-check-ss↦vs >>= return refl) =
    (match?-s-v↦true >>= return refl) >>=
    (Lens.GetPut elem-lens get-s↦v >>= match?-s-v↦true >>= assert refl then proj₁ all >>= assert refl then return refl) >>=
    GetPut-align vs ss (proj₂ all) mapPar-get-and-check-ss↦vs >>= return refl

  GetPut : {ss : List S} {vs : List V} → get ss ↦ vs → put ss vs ↦ ss
  GetPut (filterᴾ-comp >>= mapPar-comp) =
    filterᴾ-comp >>=
    GetPut-align _ _ (filterᴾ-all-true filterᴾ-comp) mapPar-comp >>=
    return (filterᴾ-unfilterᴾ-inverse source-condition _ filterᴾ-comp)

align-lens : {S V : Set} (source-condition : S → Par Bool) (match? : S → V → Par Bool)
             (elem-lens : S ⇆ V) (create : V → Par S) (conceal : S → Par (Maybe S)) → List S ⇆ List V
align-lens source-condition match? elem-lens create conceal =
  record { put = put; get = get; PutGet = PutGet; GetPut = GetPut }
  where open AlignLens source-condition match? elem-lens create conceal
