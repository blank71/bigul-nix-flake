module DynamicallyChecked.ViewCase (S V : Set) where

open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Lens

open import Function
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.Fin
open import Data.List
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


get-and-check : {n : ℕ} → (S ⇆ V) → (V → Par (Fin (suc n))) → S → Par V
get-and-check l lsel s = Lens.get l s >>= λ v → lsel v >>= λ i → assert (i ==ᶠ zero) then return v

restrict : {n : ℕ} → (V → Par (Fin (suc n))) → V → Par (Fin n)
restrict lsel = embed ∘ pred' <=< lsel

put-branch-check : {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → Fin n → S → Par S
put-branch-check ls       lsel zero    s = return s
put-branch-check (l ∷ ls) lsel (suc i) s = catch (get-and-check l lsel s) (const fail) (put-branch-check ls (restrict lsel) i s)

put : {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → S → V → Par S
put ls lsel s v = lsel v >>= λ i → Lens.put (lookup i ls) s v >>= put-branch-check ls lsel i

get : {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → S → Par V
get []       lsel s = fail
get (l ∷ ls) lsel s = catch (get-and-check l lsel s) return (get ls (restrict lsel) s)

put-branch-check-eq : {n : ℕ} (ls : Vec (S ⇆ V) n) (lsel : V → Par (Fin n)) (i : Fin n) {s s' : S} → put-branch-check ls lsel i s ↦ s' → s ≡ s'
put-branch-check-eq ls       lsel zero    (return eq       ) = eq
put-branch-check-eq (l ∷ ls) lsel (suc i) (catch-fst _ ()  )
put-branch-check-eq (l ∷ ls) lsel (suc i) (catch-snd _ comp) = put-branch-check-eq ls (restrict lsel) i comp

PutGet : {n : ℕ} (ls : Vec (S ⇆ V) n) (lsel : V → Par (Fin n)) {s s' : S} {v : V} → put ls lsel s v ↦ s' → get ls lsel s' ↦ v
PutGet []       lsel (_>>=_ {x = ()   } _ _)
PutGet (l ∷ ls) lsel (_>>=_ {x = zero } lsel↦ (put↦ >>= return refl)) =
  catch-fst (Lens.PutGet l put↦ >>= lsel↦ >>= assert refl then return refl) (return refl)
PutGet (l ∷ ls) lsel (_>>=_ {x = suc i} lsel↦ (put↦ >>= catch-fst _ ()))
PutGet (l ∷ ls) lsel (_>>=_ {x = suc i} lsel↦ (put↦ >>= catch-snd get-and-check↦ᶠ put-branch-check↦))
  with put-branch-check-eq ls (restrict lsel) i put-branch-check↦
PutGet (l ∷ ls) lsel (_>>=_ {x = suc i} lsel↦ (put↦ >>= catch-snd get-and-check↦ᶠ put-branch-check↦)) | refl =
  catch-snd get-and-check↦ᶠ (PutGet ls (restrict lsel) ((lsel↦ >>= return refl) >>= put↦ >>= put-branch-check↦))

GetPut : {n : ℕ} (ls : Vec (S ⇆ V) n) (lsel : V → Par (Fin n)) {s : S} {v : V} → get ls lsel s ↦ v → put ls lsel s v ↦ s
GetPut []       lsel ()
GetPut (l ∷ ls) lsel (catch-fst (get↦ >>= lsel↦ >>= assert eq then return refl) (return refl)) with eqFin eq
GetPut (l ∷ ls) lsel (catch-fst (get↦ >>= lsel↦ >>= assert eq then return refl) (return refl)) | refl =
  lsel↦ >>= Lens.GetPut l get↦ >>= return refl
GetPut (l ∷ ls) lsel (catch-snd fcomp comp) with GetPut ls (restrict lsel) comp
GetPut (l ∷ ls) lsel (catch-snd fcomp comp) | (_>>=_ {x = zero } lsel↦ ()) >>= _
GetPut (l ∷ ls) lsel (catch-snd fcomp comp) | (_>>=_ {x = suc i} lsel↦ (return refl)) >>= put↦ >>= put-branch-check↦
  with put-branch-check-eq ls (restrict lsel) i put-branch-check↦
GetPut (l ∷ ls) lsel (catch-snd fcomp comp) | (_>>=_ {x = suc i} lsel↦ (return refl)) >>= put↦ >>= put-branch-check↦ | refl =
  lsel↦ >>= put↦ >>= (catch-snd fcomp put-branch-check↦)

caseV-lens : {n : ℕ} → Vec (S ⇆ V) n → (V → Par (Fin n)) → S ⇆ V
caseV-lens ls lsel = record { put = put ls lsel; get = get ls lsel; PutGet = PutGet ls lsel; GetPut = GetPut ls lsel }
