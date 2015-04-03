module DynamicallyChecked.ViewCase (S V : Set) where

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
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


Branch : Set₁
Branch = Σ[ V' ∈ Set ] (S ⇆ V') × (V' ≅ V)

BranchSelector : List Branch → Set
BranchSelector []              = ⊤
BranchSelector ((V' , _) ∷ bs) = (V' → Bool) × BranchSelector bs

revcatᵇˢ : (bs' : List Branch) → BranchSelector bs' → (bs : List Branch) → BranchSelector bs → BranchSelector (revcat bs' bs)
revcatᵇˢ []               bsel'  bs bsel = bsel
revcatᵇˢ (b' ∷ bs') (p' , bsel') bs bsel = revcatᵇˢ bs' bsel' (b' ∷ bs) (p' , bsel)

get-and-check : {V' : Set} → S ⇆ V' → V' ≅ V → (V' → Bool) → S → Par V
get-and-check lens iso p s = Lens.get lens s >>= λ v' → assert p v' then Iso.to iso v'

branch-check : {V V' : Set} → V' ≅ V → (V' → Bool) → V → Par V'
branch-check iso p v = Iso.from iso v >>= λ v' → assert p v' then return v'

put : (bs : List Branch) → BranchSelector bs → S → V → Par S
put []                            bsel  s v = fail
put ((V' , lens , iso) ∷ bs) (p , bsel) s v =
  catch (branch-check iso p v) (Lens.put lens s)
        (put bs bsel s v >>= λ s' → catch (get-and-check lens iso p s') (const fail) (return s'))

get : (bs : List Branch) → BranchSelector bs → S → Par V
get []                            bsel  s = fail
get ((V' , lens , iso) ∷ bs) (p , bsel) s = catch (get-and-check lens iso p s) return (get bs bsel s >>= λ v → catch (branch-check iso p v) (const fail) (return v))

PutGet : (bs : List Branch) (bsel : BranchSelector bs) {s s' : S} {v : V} → put bs bsel s v ↦ s' → get bs bsel s' ↦ v
PutGet []                            bsel  ()
PutGet ((V' , lens , iso) ∷ bs) (p , bsel) (catch-fst (from-v↦v' >>= assert p-v'≡true then return refl) l-put-s-v'↦s') =
  catch-fst (Lens.PutGet lens l-put-s-v'↦s' >>= assert p-v'≡true then Iso.from-to-inverse iso from-v↦v') (return refl)
PutGet ((V' , lens , iso) ∷ bs) (p , bsel) (catch-snd branch-check↦ᶠ (put↦ >>= catch-fst _ ()))
PutGet ((V' , lens , iso) ∷ bs) (p , bsel) (catch-snd branch-check↦ᶠ (put↦ >>= catch-snd get-and-check↦ᶠ (return refl))) =
  catch-snd get-and-check↦ᶠ (PutGet bs bsel put↦ >>= catch-snd branch-check↦ᶠ (return refl))

GetPut : (bs : List Branch) (bsel : BranchSelector bs) {s : S} {v : V} → get bs bsel s ↦ v → put bs bsel s v ↦ s
GetPut []            bsel  () 
GetPut ((V' , lens , iso) ∷ bs) (p , bsel) (catch-fst (l-get-s↦v' >>= assert p-v'≡true then to-v'↦v) (return refl)) =
  catch-fst (Iso.to-from-inverse iso to-v'↦v >>= assert p-v'≡true then return refl) (Lens.GetPut lens l-get-s↦v')
GetPut ((V' , lens , iso) ∷ bs) (p , bsel) (catch-snd get-and-check↦ᶠ (get↦ >>= catch-fst _ ()))
GetPut ((V' , lens , iso) ∷ bs) (p , bsel) (catch-snd get-and-check↦ᶠ (get↦ >>= catch-snd branch-check↦ᶠ (return refl))) =
  catch-snd branch-check↦ᶠ (GetPut bs bsel get↦ >>= catch-snd get-and-check↦ᶠ (return refl))

caseV-lens : (bs : List Branch) → BranchSelector bs → S ⇆ V
caseV-lens bs bsel = record { put = put bs bsel; get = get bs bsel; PutGet = PutGet bs bsel; GetPut = GetPut bs bsel }
