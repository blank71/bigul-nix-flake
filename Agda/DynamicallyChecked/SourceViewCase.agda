open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module DynamicallyChecked.SourceViewCase (S V : Set) (dec : Decidable (_≡_ {A = V})) where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Lens

open import Function
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.Fin
open import Data.List


Branch : Set₁
Branch = (S → V → Par Bool) × (S ⇆ V)

get-selected : (S → V → Par Bool) → S ⇆ V → S → Par V
get-selected p l s = Lens.get l s >>= λ v → p s v >>= λ matched → assert matched then return v

put : (bs : List Branch) → S → V → Par S
put []             s v = fail
put ((p , l) ∷ bs) s v = p s v >>= λ matched →
                         if matched then (Lens.put l s v >>= λ s' →
                                          p s' v >>= λ matched' →
                                          assert matched' then return s')
                                    else (put bs s v >>= λ s' →
                                          p s' v >>= λ matched' →
                                          assert-not matched' then
                                          catch (get-selected p l s') (const fail) (return s'))

get : (bs : List Branch) → S → Par V
get []             s = fail
get ((p , l) ∷ bs) s = catch (get-selected p l s) return 
                             (get bs s >>= λ v → p s v >>= λ matched → assert-not matched then return v)

PutGet : (bs : List Branch) {s s' : S} {v : V} → put bs s v ↦ s' → get bs s' ↦ v
PutGet []             ()
PutGet ((p , l) ∷ bs) (_>>=_ {x = false} p-s-v↦false (put-s-v↦s' >>= p-s'-v↦false >>= assert-not refl then catch-fst comp ()))
PutGet ((p , l) ∷ bs) (_>>=_ {x = false} p-s-v↦false (put-s-v↦s' >>= p-s'-v↦false >>= assert-not refl then catch-snd fcomp (return refl))) =
  catch-snd fcomp (PutGet bs put-s-v↦s' >>= p-s'-v↦false >>= assert-not refl then return refl)
PutGet ((p , l) ∷ bs) (_>>=_ {x = true } p-s-v↦true (put-l-s-v↦s' >>= p-s'-v↦true >>= assert refl then return refl)) =
  catch-fst (Lens.PutGet l put-l-s-v↦s' >>= p-s'-v↦true >>= assert refl then return refl) (return refl)

GetPut : (bs : List Branch) {s : S} {v : V} → get bs s ↦ v → put bs s v ↦ s
GetPut []             () 
GetPut ((p , l) ∷ bs) (catch-fst (get-l-s↦v >>= p-s-v↦true >>= assert refl then return refl) (return refl)) =
  p-s-v↦true >>= Lens.GetPut l get-l-s↦v >>= p-s-v↦true >>= assert refl then return refl
GetPut ((p , l) ∷ bs) (catch-snd fcomp (get-s↦v >>= p-s-v↦false >>= assert-not refl then return refl)) =
  p-s-v↦false >>= GetPut bs get-s↦v >>= p-s-v↦false >>= assert-not refl then catch-snd fcomp (return refl)

caseSV-lens : (bs : List Branch) → S ⇆ V
caseSV-lens bs = record { put = put bs; get = get bs; PutGet = PutGet bs; GetPut = GetPut bs }
