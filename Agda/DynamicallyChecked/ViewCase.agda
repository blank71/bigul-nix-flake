open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module DynamicallyChecked.ViewCase (S V : Set) (dec : Decidable (_≡_ {A = V})) where

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
Branch = Σ[ V' ∈ Set ] (S ⇆ V') × (V' ≅ V)

get-selected : {V' : Set} → S ⇆ V' → V' ≅ V → S → Par V
get-selected lens iso s = Lens.get lens s >>= Iso.to iso

put : (bs : List Branch) → S → V → Par S
put []                       s v = fail
put ((V' , lens , iso) ∷ bs) s v = catch (Iso.from iso v) (Lens.put lens s)
                                         (put bs s v >>= λ s' → catch (get-selected lens iso s')
                                                                      (λ v' → case dec v v' of (λ { (yes _) → return s'
                                                                                                  ; (no  _) → fail }))
                                                                      (return s'))

get : (bs : List Branch) → S → Par V
get []                       s = fail
get ((V' , lens , iso) ∷ bs) s = catch (get-selected lens iso s) return
                                       (get bs s >>= λ v → catch (Iso.from iso v) (const fail) (return v))

PutGet : (bs : List Branch) {s s' : S} {v : V} → put bs s v ↦ s' → get bs s' ↦ v
PutGet []                       ()
PutGet ((V' , lens , iso) ∷ bs) (catch-fst from-v↦v' l-put-s-v'↦s') =
  catch-fst (Lens.PutGet lens l-put-s-v'↦s' >>= Iso.from-to-inverse iso from-v↦v') (return refl)
PutGet ((V' , lens , iso) ∷ bs) {v = v} (catch-snd from↦ᶠ (l-put↦ >>= catch-fst {x = v'} _ comp)) with dec v v'
PutGet ((V' , lens , iso) ∷ bs) (catch-snd from↦ᶠ (l-put↦ >>= catch-fst get↦ (return refl))) | yes refl =
  catch-fst get↦ (return refl)
PutGet ((V' , lens , iso) ∷ bs) {v = v} (catch-snd from↦ᶠ (l-put↦ >>= catch-fst {x = v'} _ ())) | no  _
PutGet ((V' , lens , iso) ∷ bs) (catch-snd from↦ᶠ (l-put↦ >>= catch-snd get-selected↦ᶠ (return refl))) =
  catch-snd get-selected↦ᶠ (PutGet bs l-put↦ >>= catch-snd from↦ᶠ (return refl))

GetPut : (bs : List Branch) {s : S} {v : V} → get bs s ↦ v → put bs s v ↦ s
GetPut []                       () 
GetPut ((V' , lens , iso) ∷ bs) (catch-fst (l-get-s↦v' >>= to-v'↦v) (return refl)) =
  catch-fst (Iso.to-from-inverse iso to-v'↦v) (Lens.GetPut lens l-get-s↦v')
GetPut ((V' , lens , iso) ∷ bs) (catch-snd get-selected↦ᶠ (get↦ >>= catch-fst _ ()))
GetPut ((V' , lens , iso) ∷ bs) (catch-snd get-selected↦ᶠ (get↦ >>= catch-snd from↦ᶠ (return refl))) =
  catch-snd from↦ᶠ (GetPut bs get↦ >>= catch-snd get-selected↦ᶠ (return refl))

caseV-lens : (bs : List Branch) → S ⇆ V
caseV-lens bs = record { put = put bs; get = get bs; PutGet = PutGet bs; GetPut = GetPut bs }
