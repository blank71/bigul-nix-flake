module HoareLogic.Test where

open import Agda.Primitive
open import Function
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.List as List
open import Data.String
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


record ⊤ {l : Level} : Set l where
  constructor tt
  
data ⊥ {l : Level} : Set l where

mutual

  data Branch (S V : Set) : Set₁ where
    normal   : BiGUL S V → (S → Bool) → Branch S V
    adaptive : (S → V → S) → Branch S V

  data BiGUL : Set → Set → Set₁ where
    skip   : {S : Set} → BiGUL S ⊤
    dep    : {S V  V' : Set} → BiGUL S V → (S → V → V') → BiGUL S (V × V')
    rearrV : {S V V' : Set} → (V → V') → BiGUL S V' → BiGUL S V
    case   : {S V : Set} → List ((S → V → Bool) × Branch S V) → BiGUL S V

IsNormal : {S V : Set} → Branch S V → Set₁
IsNormal (normal _ _) = ⊤
IsNormal (adaptive _) = ⊥

emb : {S V : Set} → (S → V) → (S → V → S) → (V → V → Bool) → BiGUL S V
emb g p _≟_ = case (((λ s v → g s ≟ v) ,
                       normal (rearrV (λ v → tt , v) (dep skip (λ s _ → g s))) (λ _ → true)) ∷
                     ((λ s v → not (g s ≟ v)) ,
                       adaptive p) ∷ [])

Rel : Set → Set → Set₁
Rel A B = A → B → Set

_∩_ : {A B : Set} → Rel A B → Rel A B → Rel A B
(R ∩ S) a b = R a b × S a b

infixr 5 _∩_

idᴿ : {A : Set} → Rel A A
idᴿ x y = x ≡ y

fun : {A B : Set} → (A → B) → Rel B A
fun f b a = f a ≡ b

_ᵒ : {A B : Set} → Rel A B → Rel B A
(R ᵒ) b a = R a b

infix 6 _ᵒ

_ᵀ : {A B C : Set} → (A → B → C) → Rel A (B × C)
(f ᵀ) a (b , c) = f a b ≡ c

infix 6 _ᵀ

_∖_ : {A B C : Set} → Rel A B → Rel A C → Rel B C
(R ∖ S) b c = ∀ a → R a b → S a c

infix 5 _∖_

_·_ : {A B C : Set} → Rel A B → Rel B C → Rel A C
(R · S) a c = ∃ λ b → R a b × S b c

infixl 3 _·_

Π : {A B : Set} → Rel A B
Π _ _ = ⊤

⋃ : {A B : Set} → List (Rel A B) → Rel A B
⋃ []       _ _ = ⊥
⋃ (R ∷ Rs) a b = R a b ⊎ (⋃ Rs) a b

lift₁ : {S V : Set} → (S → Bool) → Rel S V
lift₁ p s v = p s ≡ true

lift₂ : {S V : Set} → (S → V → Bool) → Rel S V
lift₂ p s v = p s v ≡ true

_⊆_ : {A B : Set} → Rel A B → Rel A B → Set
R ⊆ S = ∀ a b → R a b → S a b

data Index {l : Level} {A : Set l} : List A → Set where
  zero : {x : A} {xs : List A} → Index (x ∷ xs)
  suc  : {x : A} {xs : List A} → Index xs → Index (x ∷ xs)
  
lookup : {l : Level} {A : Set l} (xs : List A) → Index xs → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (suc i) = lookup xs i

mutual

  data HT : {S V : Set} → BiGUL S V → Rel S V → Rel S V → Set₁ where
    conseq : {S V : Set} {b : BiGUL S V} {R R' S S' : Rel S V} → HT b R R' → S ⊆ R → R' ⊆ S' → HT b S S'
    skip   : {S : Set} {R : Rel S ⊤} → HT skip R R
    dep    : {S V V' : Set} {b : BiGUL S V} {f : S → V → V'} {R : Rel S (V × V')} {R' : Rel S V} →
             HT b (R · fun proj₁ ᵒ) R' → HT (dep b f) (R ∩ (Π · (idᴿ ∩ ((R' · fun proj₁) ∖ f ᵀ)))) ((R' · fun proj₁) ∩ f ᵀ)
    rearrV : {S V V' : Set} {f : V → V'} {b : BiGUL S V'} {R R' : Rel S V} →
             HT b (R · fun f ᵒ) (R' · fun f ᵒ) → HT (rearrV f b) (R ∩ (Π · fun f)) R'
    case   : {S V : Set} {branches : List ((S → V → Bool) × Branch S V)} {R R' : Rel S V} →
             casePremise branches branches R R' →
             HT (case branches) (R ∩ ⋃ (List.map (lift₂ ∘ proj₁) branches)) R'
  
  casePremise : {S V : Set} → List ((S → V → Bool) × Branch S V) → List ((S → V → Bool) × Branch S V) →
                (R R' : Rel S V) → Set₁
  casePremise []                            branches' R R' = ⊤
  casePremise ((c , normal b p) ∷ branches) branches' R R' = HT b (R ∩ lift₂ c) (R' ∩ lift₂ c ∩ lift₁ p) ×
                                                             casePremise branches branches' R R'
  casePremise ((c , adaptive f) ∷ branches) branches' R R' =
    (∀ s v → (R ∩ lift₂ c) s v → ∃ (λ i → let c' , branch = lookup branches' i
                                          in IsNormal branch × c' (f s v) v ≡ true)) ×
    casePremise branches branches' R R'

rearrV' : {S V V' : Set} {f : V → V'} {b : BiGUL S V'} {R R' : Rel S V} →
          HT b (R · fun f ᵒ) (R' · fun f ᵒ) → R ⊆ (Π · fun f) → HT (rearrV f b) R R'
rearrV' ht sse = conseq (rearrV ht) (λ s v r → r , sse s v r) (λ s v r' → r')

postulate trustMe : {l : Level} {A : Set l} (reason : String) → A

embed-derivation : {S V : Set} (s₀ : S) (g : S → V) (p : S → V → S) (dec : V → V → Bool) →
                   HT (emb g p dec) (λ s v → s ≡ s₀) (λ s' v → p s₀ v ≡ s')
embed-derivation {S} {V} s₀ g p dec = conseq (case (conseq (rearrV (conseq (dep (conseq skip (λ { s tt (_ , (_ , (pf , _) , _) , _) → pf }) (λ s v → id))) (λ { s (tt , v) pf → pf , (tt , v) , (tt , refl , (λ s' _ → trustMe "g s₀ ≡ v from pf")) }) (λ { s (tt , v) ((tt , s≡s₀ , _) , g-s≡v) → v , (trustMe "GetPut" , trustMe "g-s≡-v" , refl) , refl }))) (λ s v pf → pf , (tt , v) , tt , refl) (λ s v → id) , (λ s v pf → zero , tt , trustMe "PutGet") , tt)) see-below₀ (λ _ _ → id)
 where
   see-below₀ : (s : S) (v : V) → s ≡ s₀ → (s ≡ s₀) × (dec (g s) v ≡ true ⊎ not (dec (g s) v) ≡ true ⊎ ⊥)
   see-below₀ .s₀ v refl = refl , trustMe "dec decidable"
