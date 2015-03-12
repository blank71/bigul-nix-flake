module DynamicallyChecked.SourceCase where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Level
open import Function
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin
open import Data.Vec using (Vec; lookup)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


data Branch (S V : Set) : Set₁ where
  normal   : S ⇆ V → Branch S V
  adaptive : (S → Par S) → Branch S V

branch : {S V : Set} {l : Level} {A : Set l} → (S ⇆ V → A) → ((S → Par S) → A) → Branch S V → A
branch f g (normal   l) = f l
branch f g (adaptive u) = g u

elim-branch-normal :
  {S V : Set} {ℓ ℓ' : Level} {A : Set ℓ} {f : S ⇆ V → A} {g : (S → Par S) → A} {b : Branch S V} {l : S ⇆ V} →
  b ≡ normal l → (P : A → Set ℓ') → P (f l) → P (branch f g b)
elim-branch-normal refl P p = p

module CaseS {S V : Set} {n : ℕ} (bs : Vec (Branch S V) n) (bsel : S → Par (Fin n)) where

  put-normal-branch : S → V → Fin n → S ⇆ V → Par S
  put-normal-branch s v i l = Lens.put l s v >>= λ s' → bsel s' >>= λ j → assert (i ==ᶠ j) then return s'

  put-with-adaptation : S → V → ((S → Par S) → Par S) → Par S
  put-with-adaptation s v g = bsel s >>= λ i → branch (put-normal-branch s v i) g (lookup i bs)

  put : S → V → Par S
  put s v = put-with-adaptation s v (λ u → u s >>= λ s' → put-with-adaptation s' v (const fail))

  get : S → Par V
  get s = bsel s >>= branch (λ l → Lens.get l s) (const fail) ∘ flip lookup bs

  PutGet-normal : {s : S} {v : V} {s' : S}
                  {i : Fin n} → bsel s ↦ i →
                  (l : S ⇆ V) → lookup i bs ≡ normal l →
                  put-normal-branch s v i l ↦ s' →
                  get s' ↦ v
  PutGet-normal {v = v} bsel-s↦i l lookup-i-bs≡normal-l (put-s-v↦s' >>= bsel-s'↦j >>= assert i==ᶠj≡true then return refl)
      with eqFin i==ᶠj≡true
  ... | refl = bsel-s'↦j >>= elim-branch-normal lookup-i-bs≡normal-l (flip CompSeq v) (Lens.PutGet l put-s-v↦s')

  PutGet : {s : S} {v : V} {s' : S} → put s v ↦ s' → get s' ↦ v
  PutGet (_>>=_ {x = i} bsel-s↦i comp)
    with lookup i bs | inspect (lookup i) bs
  PutGet (bsel-s↦i >>= put-normal-branch-comp)
    | normal l | [ lookup-i-bs≡normal-l ] = PutGet-normal bsel-s↦i l lookup-i-bs≡normal-l put-normal-branch-comp
  PutGet (bsel-s↦i >>= u-s↦s' >>= (_>>=_ {x = j} bsel-s'↦j put-normal-branch-comp))
    | adaptive _ | _ with lookup j bs | inspect (lookup j) bs
  PutGet (bsel-s↦i >>= u-s↦s' >>= (_>>=_ {x = j} bsel-s'↦j put-normal-branch-comp))
    | adaptive _ | _ | normal l' | [ lookup-j-bs≡normal-l' ] = PutGet-normal bsel-s'↦j l' lookup-j-bs≡normal-l' put-normal-branch-comp
  PutGet (bsel-s↦i >>= u-s↦s' >>= (_>>=_ {x = j} bsel-s'↦j ()))
    | adaptive _ | _ | adaptive _ | _

  GetPut : {s : S} {v : V} → get s ↦ v → put s v ↦ s
  GetPut (_>>=_ {x = i} bsel-s↦i comp) with lookup i bs | inspect (lookup i) bs
  GetPut {s} (bsel-s↦i >>= get-s↦v) | normal   l | [ lookup-i-bs≡normal-l ] =
    bsel-s↦i >>= elim-branch-normal lookup-i-bs≡normal-l (flip CompSeq s)
                   (Lens.GetPut l get-s↦v >>= bsel-s↦i >>= assert (==ᶠ-reflexive refl) then return refl)
  GetPut (bsel-s↦i >>= ()     ) | adaptive _ | _

caseS-lens : {S V : Set} {n : ℕ} → Vec (Branch S V) n → (S → Par (Fin n)) → S ⇆ V
caseS-lens bs bsel = record { put = put; get = get; PutGet = PutGet; GetPut = GetPut }
  where open CaseS bs bsel
