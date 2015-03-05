module DynamicallyChecked.SourceCase where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

open import Function
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin
open import Data.Vec
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


data Branch (S V : Set) : Set where
  normal   : S ⇆ V → Branch S V
  adaptive : (S → Maybe S) → Branch S V

branch : {S V A : Set} → (S ⇆ V → A) → ((S → Maybe S) → A) → Branch S V → A
branch f g (normal   l) = f l
branch f g (adaptive u) = g u

reduce-branch-normal : {S V A : Set} {f : S ⇆ V → A} {g : (S → Maybe S) → A} {b : Branch S V} {l : S ⇆ V} →
                       b ≡ normal l → branch f g b ≡ f l
reduce-branch-normal refl = refl

module CaseS {S V : Set} {n : ℕ} (bs : Vec (Branch S V) n) (bsel : S → Maybe (Fin n)) where

  put-branch-check : S → Fin n → Fin n → Maybe S
  put-branch-check s i j with i ≟ᶠ j
  put-branch-check s i j | yes _ = just s
  put-branch-check s i j | no  _ = nothing

  put-branch-check-equal : (s : S) (i : Fin n) → put-branch-check s i i ≡ᴶ s
  put-branch-check-equal s i with i ≟ᶠ i
  put-branch-check-equal s i | yes _   = refl
  put-branch-check-equal s i | no  i≢i with i≢i refl
  put-branch-check-equal s i | no  i≢i | ()

  put-normal-branch : S → V → Fin n → S ⇆ V → Maybe S
  put-normal-branch s v i l = Lens.put l s v ↪ λ s' → bsel s' ↪ put-branch-check s' i

  put-with-adaptation : S → V → ((S → Maybe S) → Maybe S) → Maybe S
  put-with-adaptation s v g = bsel s ↪ λ i → branch (put-normal-branch s v i) g (lookup i bs)

  put : S → V → Maybe S
  put s v = put-with-adaptation s v (λ u → u s ↪ λ s' → put-with-adaptation s' v (const nothing))

  get : S → Maybe V
  get s = bsel s ↪ branch (λ l → Lens.get l s) (const nothing) ∘ flip lookup bs

  PutGet-normal : (s : S) (v : V) {s' : S}
                  (i : Fin n) → bsel s ≡ᴶ i →
                  (l : S ⇆ V) → lookup i bs ≡ normal l →
                  put-normal-branch s v i l ≡ᴶ s' →
                  get s' ≡ᴶ v
  PutGet-normal s v i bsel-s≡ᴶi l lookup-i-bs≡normal-l eq with bind-equals-just (Lens.put l s v) eq
  PutGet-normal s v i bsel-s≡ᴶi l lookup-i-bs≡normal-l _  | s' , _ , eq with bind-equals-just (bsel s') eq
  PutGet-normal s v i bsel-s≡ᴶi l lookup-i-bs≡normal-l _  | s' , _ , _  | j , _ , _ with i ≟ᶠ j
  PutGet-normal s v i bsel-s≡ᴶi l lookup-i-bs≡normal-l _  | s' , put-s-v≡ᴶs' , _ | .i , bsel-s'≡ᴶi , refl | yes refl =
    begin
      bsel s' ↪ branch (λ l → Lens.get l s') (const nothing) ∘ flip lookup bs
        ≡⟨ reduce-bind bsel-s'≡ᴶi ⟩
      branch (λ l → Lens.get l s') (const nothing) (lookup i bs)
        ≡⟨ reduce-branch-normal lookup-i-bs≡normal-l ⟩
      Lens.get l s'
        ≡⟨ Lens.PutGet l s v put-s-v≡ᴶs' ⟩
      just v
    ∎
    where open ≡-Reasoning
  PutGet-normal s v i l bsel-s≡ᴶi lookup-i-bs≡normal-l _  | s' , put-s-v≡ᴶs' , _ | j , bsel-s'≡ᴶji , () | no i≢j

  PutGet : (s : S) (v : V) {s' : S} → put s v ≡ᴶ s' → get s' ≡ᴶ v
  PutGet s v eq with bind-equals-just (bsel s) eq
  PutGet s v _  | i , bsel-s≡ᴶi , eq with lookup i bs | inspect (lookup i) bs
  PutGet s v _  | i , bsel-s≡ᴶi , eq | normal   l | [ lookup-i-bs≡normal-l   ] =
    PutGet-normal s v i bsel-s≡ᴶi l lookup-i-bs≡normal-l eq
  PutGet s v _  | i , bsel-s≡ᴶi , eq | adaptive u | [ lookup-i-bs≡adaptive-u ]
                with bind-equals-just (u s) eq
  PutGet s v _  | i , bsel-s≡ᴶi , _  | adaptive u | [ lookup-i-bs≡adaptive-u ]
                | s' , u-s≡ᴶs' , eq with bind-equals-just (bsel s') eq
  PutGet s v _  | i , bsel-s≡ᴶi , _  | adaptive u | [ lookup-i-bs≡adaptive-u ]
                | s' , u-s≡ᴶs' , _  | i' , bsel-s'≡ᴶi' , eq with lookup i' bs | inspect (lookup i') bs
  PutGet s v _  | i , bsel-s≡ᴶi , _  | adaptive u | [ lookup-i-bs≡adaptive-u ]
                | s' , u-s≡ᴶs' , _  | i' , bsel-s'≡ᴶi' , eq | normal   l' | [ lookup-i'-bs≡normal-l'   ] =
    PutGet-normal s' v i' bsel-s'≡ᴶi' l' lookup-i'-bs≡normal-l' eq
  PutGet s v _  | i , bsel-s≡ᴶi , _  | adaptive u | [ lookup-i-bs≡adaptive-u ]
                | s' , u-s≡ᴶs' , _  | i' , bsel-s'≡ᴶi' , () | adaptive u' | [ lookup-i'-bs≡adaptive-u' ]

  GetPut : (s : S) {v : V} → get s ≡ᴶ v → put s v ≡ᴶ s
  GetPut s {v} eq with bind-equals-just (bsel s) eq
  GetPut s {v} _  | i , bsel-s≡ᴶi , _ with lookup i bs | inspect (lookup i) bs
  GetPut s {v} _  | i , bsel-s≡ᴶi , l-get-s≡ᴶv | normal   l | [ lookup-i-bs≡normal-l   ] =
    let g = λ u → u s ↪ λ s' → put-with-adaptation s' v (const nothing)
    in  begin
          put s v
            ≡⟨ refl ⟩
          put-with-adaptation s v g
            ≡⟨ reduce-bind bsel-s≡ᴶi ⟩
          branch (put-normal-branch s v i) g (lookup i bs)
            ≡⟨ reduce-branch-normal lookup-i-bs≡normal-l ⟩
          put-normal-branch s v i l
            ≡⟨ reduce-bind (Lens.GetPut l s l-get-s≡ᴶv) ⟩
          bsel s ↪ put-branch-check s i
            ≡⟨ reduce-bind bsel-s≡ᴶi ⟩
          put-branch-check s i i
            ≡⟨ put-branch-check-equal s i ⟩
          just s
        ∎
    where open ≡-Reasoning
  GetPut s {v} _  | i , bsel-s≡ᴶi , ()         | adaptive u | [ lookup-i-bs≡adaptive-u ]

caseS-lens : {S V : Set} {n : ℕ} → Vec (Branch S V) n → (S → Maybe (Fin n)) → S ⇆ V
caseS-lens bs bsel = record { put = put; get = get; PutGet = PutGet; GetPut = GetPut }
  where open CaseS bs bsel
