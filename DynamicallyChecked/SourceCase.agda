module DynamicallyChecked.SourceCase (S V : Set) where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Level
open import Function
open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality


data BranchType (S' : Set) : Set₁ where
  normal   : (S' ⇆ V) → BranchType S'
  adaptive : (S' → Par S) → BranchType S'

Branch : Set₁
Branch = Σ[ S' ∈ Set ] (S ⇆ S') × BranchType S'

elimBranchType : {S' : Set} {l : Level} {A : Set l} → ((S' ⇆ V) → A) → ((S' → Par S) → A) → BranchType S' → A
elimBranchType f g (normal   l) = f l
elimBranchType f g (adaptive u) = g u

put-with-adaptation : List Branch → S → V → (S → Par S) → Par S
put-with-adaptation []                      s v f = fail
put-with-adaptation ((S' , lens , bt) ∷ bs) s v f =
  catch (Lens.get lens s)
        (λ s' → elimBranchType (λ lens' → Lens.put lens' s' v >>= Lens.put lens s) (λ u → u s' >>= f) bt)
        (put-with-adaptation bs s v f >>= λ s' → catch (Lens.get lens s') (const fail) (return s'))

put : List Branch → S → V → Par S
put bs s v = put-with-adaptation bs s v (λ s' → put-with-adaptation bs s' v (const fail))

get : List Branch → S → Par V
get []                      s = fail
get ((S' , lens , bt) ∷ bs) s =
  catch (Lens.get lens s) (elimBranchType Lens.get (const (const fail)) bt) (get bs s)

UnmatchedBranches : List Branch → S → Set₁
UnmatchedBranches []                     s = ⊤
UnmatchedBranches ((S' , lens , b) ∷ bs) s = FailedCompSeq (Lens.get lens s) × UnmatchedBranches bs s

get-revcat : (bs : List Branch) {s : S} {v : V} (bs' : List Branch) → UnmatchedBranches bs' s →
             get bs s ↦ v → get (revcat bs' bs) s ↦ v
get-revcat bs []                      ub  get↦ = get↦
get-revcat bs (b ∷ bs') (lens-get↦ᶠ , ub) get↦ = get-revcat (b ∷ bs) bs' ub (catch-snd lens-get↦ᶠ get↦)

PutGet-with-adaptation' :
  (bs : List Branch) {s : S} {v : V} {s' : S} → put-with-adaptation bs s v (const fail) ↦ s' → get bs s' ↦ v
PutGet-with-adaptation' []                                ()
PutGet-with-adaptation' ((S' , lens , normal lens') ∷ bs) (catch-fst lens-get↦ (lens'-put↦ >>= lens-put↦)) =
  catch-fst (Lens.PutGet lens lens-put↦) (Lens.PutGet lens' lens'-put↦)
PutGet-with-adaptation' ((S' , lens , normal lens') ∷ bs) (catch-snd _ (_ >>= catch-fst _ ()))
PutGet-with-adaptation' ((S' , lens , normal lens') ∷ bs)
  (catch-snd lens-get-s↦ᶠ (put-with-adaptation↦ >>= catch-snd lens-get-s'↦ᶠ (return refl))) =
  catch-snd lens-get-s'↦ᶠ (PutGet-with-adaptation' bs put-with-adaptation↦)
PutGet-with-adaptation' ((S' , lens , adaptive u  ) ∷ bs) (catch-fst _ (_ >>= ()))
PutGet-with-adaptation' ((S' , lens , adaptive u  ) ∷ bs) (catch-snd x (_ >>= catch-fst _ ()))
PutGet-with-adaptation' ((S' , lens , adaptive u  ) ∷ bs)
  (catch-snd lens-get-s↦ᶠ (put-with-adaptation↦ >>= catch-snd lens-get-s'↦ᶠ (return refl))) =
  catch-snd lens-get-s'↦ᶠ (PutGet-with-adaptation' bs put-with-adaptation↦)

PutGet-with-adaptation :
  (bs : List Branch) {s : S} {v : V} {s' : S} (bs' : List Branch) → UnmatchedBranches bs' s' →
  put-with-adaptation bs s v (λ s'' → put-with-adaptation (revcat bs' bs) s'' v (const fail)) ↦ s' →
  get (revcat bs' bs) s' ↦ v
PutGet-with-adaptation []                                bs' ub ()
PutGet-with-adaptation ((S' , lens , normal lens') ∷ bs) bs' ub (catch-fst lens-get↦ (lens'-put↦ >>= lens-put↦)) =
  get-revcat ((S' , lens , normal lens') ∷ bs) bs' ub
    (catch-fst (Lens.PutGet lens lens-put↦) (Lens.PutGet lens' lens'-put↦))
PutGet-with-adaptation ((S' , lens , normal lens') ∷ bs) bs' ub
  (catch-snd lens-get↦ᶠ (put-with-adaptation↦ >>= catch-fst _ ()))
PutGet-with-adaptation ((S' , lens , normal lens') ∷ bs) bs' ub
  (catch-snd lens-get-s↦ᶠ (put-with-adaptation↦ >>= catch-snd lens-get-s'↦ᶠ (return refl))) =
  PutGet-with-adaptation bs ((S' , lens , normal lens') ∷ bs') (lens-get-s'↦ᶠ , ub) put-with-adaptation↦
PutGet-with-adaptation ((S' , lens , adaptive u  ) ∷ bs) bs' ub (catch-fst lens-get↦ (u↦ >>= put-with-adaptation↦)) =
  PutGet-with-adaptation' (revcat bs' ((S' , lens , adaptive u) ∷ bs)) put-with-adaptation↦
PutGet-with-adaptation ((S' , lens , adaptive u  ) ∷ bs) bs' ub
  (catch-snd lens-get-s↦ᶠ (put-with-adaptation↦ >>= catch-fst lens-get↦ ()))
PutGet-with-adaptation ((S' , lens , adaptive u  ) ∷ bs) bs' ub
  (catch-snd lens-get-s↦ᶠ (put-with-adaptation↦ >>= catch-snd lens-get-s'↦ᶠ (return refl))) =
  PutGet-with-adaptation bs ((S' , lens , adaptive u) ∷ bs') (lens-get-s'↦ᶠ , ub) put-with-adaptation↦

PutGet : (bs : List Branch) {s : S} {v : V} {s' : S} → put bs s v ↦ s' → get bs s' ↦ v
PutGet bs = PutGet-with-adaptation bs [] tt

-- elim-branch-normal :
--   {S V : Set} {ℓ ℓ' : Level} {A : Set ℓ} {f : S ⇆ V → A} {g : (S → Par S) → A} {b : Branch S V} {l : S ⇆ V} →
--   b ≡ normal l → (P : A → Set ℓ') → P (f l) → P (branch f g b)
-- elim-branch-normal refl P p = p

-- module CaseS {S V : Set} {n : ℕ} (bs : Vec (Branch S V) n) (bsel : S → Par (Fin n)) where

--   put-normal-branch : S → V → Fin n → S ⇆ V → Par S
--   put-normal-branch s v i l = Lens.put l s v >>= λ s' → bsel s' >>= λ j → assert (i ==ᶠ j) then return s'

--   put-with-adaptation : S → V → ((S → Par S) → Par S) → Par S
--   put-with-adaptation s v g = bsel s >>= λ i → branch (put-normal-branch s v i) g (lookup i bs)

--   put : S → V → Par S
--   put s v = put-with-adaptation s v (λ u → u s >>= λ s' → put-with-adaptation s' v (const fail))

--   get : S → Par V
--   get s = bsel s >>= branch (λ l → Lens.get l s) (const fail) ∘ flip lookup bs

--   PutGet-normal : {s : S} {v : V} {s' : S}
--                   {i : Fin n} → bsel s ↦ i →
--                   (l : S ⇆ V) → lookup i bs ≡ normal l →
--                   put-normal-branch s v i l ↦ s' →
--                   get s' ↦ v
--   PutGet-normal {v = v} bsel-s↦i l lookup-i-bs≡normal-l (put-s-v↦s' >>= bsel-s'↦j >>= assert i==ᶠj≡true then return refl)
--       with eqFin i==ᶠj≡true
--   ... | refl = bsel-s'↦j >>= elim-branch-normal lookup-i-bs≡normal-l (flip CompSeq v) (Lens.PutGet l put-s-v↦s')

--   PutGet : {s : S} {v : V} {s' : S} → put s v ↦ s' → get s' ↦ v
--   PutGet (_>>=_ {x = i} bsel-s↦i comp)
--     with lookup i bs | inspect (lookup i) bs
--   PutGet (bsel-s↦i >>= put-normal-branch-comp)
--     | normal l | [ lookup-i-bs≡normal-l ] = PutGet-normal bsel-s↦i l lookup-i-bs≡normal-l put-normal-branch-comp
--   PutGet (bsel-s↦i >>= u-s↦s' >>= (_>>=_ {x = j} bsel-s'↦j put-normal-branch-comp))
--     | adaptive _ | _ with lookup j bs | inspect (lookup j) bs
--   PutGet (bsel-s↦i >>= u-s↦s' >>= (_>>=_ {x = j} bsel-s'↦j put-normal-branch-comp))
--     | adaptive _ | _ | normal l' | [ lookup-j-bs≡normal-l' ] = PutGet-normal bsel-s'↦j l' lookup-j-bs≡normal-l' put-normal-branch-comp
--   PutGet (bsel-s↦i >>= u-s↦s' >>= (_>>=_ {x = j} bsel-s'↦j ()))
--     | adaptive _ | _ | adaptive _ | _

--   GetPut : {s : S} {v : V} → get s ↦ v → put s v ↦ s
--   GetPut (_>>=_ {x = i} bsel-s↦i comp) with lookup i bs | inspect (lookup i) bs
--   GetPut {s} (bsel-s↦i >>= get-s↦v) | normal   l | [ lookup-i-bs≡normal-l ] =
--     bsel-s↦i >>= elim-branch-normal lookup-i-bs≡normal-l (flip CompSeq s)
--                    (Lens.GetPut l get-s↦v >>= bsel-s↦i >>= assert (==ᶠ-reflexive refl) then return refl)
--   GetPut (bsel-s↦i >>= ()     ) | adaptive _ | _

-- caseS-lens : {S V : Set} {n : ℕ} → Vec (Branch S V) n → (S → Par (Fin n)) → S ⇆ V
-- caseS-lens bs bsel = record { put = put; get = get; PutGet = PutGet; GetPut = GetPut }
--   where open CaseS bs bsel
