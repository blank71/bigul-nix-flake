module DynamicallyChecked.ListAlignment where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Function
open import Data.Bool
import Data.Maybe as Maybe; open Maybe
import Data.Product as Product; open Product
open import Data.List
open import Relation.Binary.PropositionalEquality


filterMaybe : {A : Set} → (A → Maybe Bool) → List A → Maybe (List A × List (Maybe A))
filterMaybe p []       = just ([] , [])
filterMaybe p (x ∷ xs) = p x ↪ λ b → Maybe.map (if b then Product.map (_∷_ x) (_∷_ nothing)
                                                     else Product.map id      (_∷_ (just x)))
                                               (filterMaybe p xs)

condense : {A : Set} → List (Maybe A) → List A
condense []              = []
condense (nothing ∷ mxs) = condense mxs
condense (just x  ∷ mxs) = x ∷ condense mxs

invert-filterMaybe : {A : Set} → List A → List (Maybe A) → List A
invert-filterMaybe xs       []              = xs
invert-filterMaybe []       (my      ∷ mys) = condense (my ∷ mys)
invert-filterMaybe (x ∷ xs) (nothing ∷ mys) = x ∷ invert-filterMaybe xs mys
invert-filterMaybe (x ∷ xs) (just y  ∷ mys) = y ∷ invert-filterMaybe (x ∷ xs) mys

condense-inverse : {A : Set} (p : A → Maybe Bool) (xs : List A) {mys : List (Maybe A)} →
                   filterMaybe p xs ≡ᴶ ([] , mys) → condense mys ≡ xs
condense-inverse p []       refl = refl
condense-inverse p (x ∷ xs) eq with bind-equals-just (p x) eq
condense-inverse p (x ∷ xs) _  | true  , p-x≡ᴶtrue  , eq with fmap-equals-just (filterMaybe p xs) eq
condense-inverse p (x ∷ xs) _  | true  , p-x≡ᴶtrue  , _  | (xs' , mys) , filterMaybe-p-xs≡ᴶxs',mys , ()
condense-inverse p (x ∷ xs) _  | false , p-x≡ᴶfalse , eq with fmap-equals-just (filterMaybe p xs) eq
condense-inverse p (x ∷ xs) _  | false , p-x≡ᴶfalse , _  | (.[] , mys) , filterMaybe-p-xs≡ᴶ[],mys , refl =
  cong (_∷_ x) (condense-inverse p xs filterMaybe-p-xs≡ᴶ[],mys)

filterMaybe-inverse : {A : Set} (p : A → Maybe Bool) (xs : List A) {xs' : List A} {mys : List (Maybe A)} →
                      filterMaybe p xs ≡ᴶ (xs' , mys) → invert-filterMaybe xs' mys ≡ xs
filterMaybe-inverse p []       refl = refl
filterMaybe-inverse p (x ∷ xs) eq with bind-equals-just (p x) eq
filterMaybe-inverse p (x ∷ xs) _  | true  , p-x≡ᴶtrue  , eq with fmap-equals-just (filterMaybe p xs) eq
filterMaybe-inverse p (x ∷ xs) _  | true  , p-x≡ᴶtrue  , _  | (xs' , mys) , filterMaybe-p-xs≡ᴶxs',mys , refl =
  cong (_∷_ x) (filterMaybe-inverse p xs filterMaybe-p-xs≡ᴶxs',mys)
filterMaybe-inverse p (x ∷ xs) _  | false , p-x≡ᴶfalse , eq with fmap-equals-just (filterMaybe p xs) eq
filterMaybe-inverse p (x ∷ xs) _  | false , p-x≡ᴶfalse , _  | ([]       , mys) , filterMaybe-p-xs≡ᴶ[],mys , refl =
  cong (_∷_ x) (condense-inverse p xs filterMaybe-p-xs≡ᴶ[],mys)
filterMaybe-inverse p (x ∷ xs) _  | false , p-x≡ᴶfalse , _  | (x' ∷ xs' , mys) , filterMaybe-p-xs≡ᴶx'∷xs',mys , refl =
  cong (_∷_ x) (filterMaybe-inverse p xs filterMaybe-p-xs≡ᴶx'∷xs',mys)

mapMaybe : {A B : Set} → (A → Maybe B) → List A → Maybe (List B)
mapMaybe f []       = just []
mapMaybe f (x ∷ xs) = f x ↪ λ y → Maybe.map (_∷_ y) (mapMaybe f xs)

module AlignLens {S V : Set} (sourceCondition : S → Maybe Bool) (isMatch : S → V → Maybe Bool)
                 (matched : S ⇆ V) (adapt : S → Maybe S) (recover : S → Maybe S) where

  put : List S → List V → Maybe (List S)
  put ss vs = filterMaybe sourceCondition ss ↪ λ { (filtered , residual) → {!!} ↪ λ ss' → just (invert-filterMaybe ss' residual) }
  
  get : List S → Maybe (List V)
  get = mapMaybe (Lens.get matched) ∘ proj₁ ↢ filterMaybe sourceCondition
