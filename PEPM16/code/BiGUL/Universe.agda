-- A universe of mutually inductive datatypes and patterns for them (Section 3.2).

module BiGUL.Universe where

open import BiGUL.Utilities
open import BiGUL.Partiality

open import Level using (Level)
open import Function using (id; const; _∘_; _∋_)
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.Fin
open import Data.List
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


data U (n : ℕ) : Set₁ where
  var  : (i : Fin n) → U n
  k    : (A : Set) (dec : Decidable (_≡_ {A = A})) → U n
  one  : U n
  _⊕_  : (F G : U n) → U n
  _⊗_  : (F G : U n) → U n
  list : (F : U n)   → U n

⟦_⟧ : {n : ℕ} → U n → (Fin n → Set) → Set
⟦ var  i  ⟧ Xs = Xs i
⟦ k A dec ⟧ Xs = A
⟦ one     ⟧ Xs = ⊤
⟦ F ⊕ G   ⟧ Xs = ⟦ F ⟧ Xs ⊎ ⟦ G ⟧ Xs
⟦ F ⊗ G   ⟧ Xs = ⟦ F ⟧ Xs × ⟦ G ⟧ Xs
⟦ list F  ⟧ Xs = List (⟦ F ⟧ Xs)

Functor : ℕ → Set₁
Functor n = Fin n → U n

data μ {n : ℕ} (F : Functor n) : Fin n → Set where
  con : {i : Fin n} → ⟦ F i ⟧ (μ F) → μ F i

decon : {n : ℕ} {F : Functor n} {i : Fin n} → μ F i → ⟦ F i ⟧ (μ F)
decon (con x) = x

decong-inj₁ : {A B : Set} {x y : A} → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
decong-inj₁ refl = refl

decong-inj₂ : {A B : Set} {x y : B} → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
decong-inj₂ refl = refl

cong-head : {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
cong-head refl = refl

cong-tail : {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
cong-tail refl = refl

mutual

  μ-dec : {n : ℕ} {F : Functor n} {i : Fin n} → Decidable (_≡_ {A = μ F i})
  μ-dec {F = F} {i} (con x) (con y) with U-dec (F i) x y
  μ-dec {F = F} {i} (con x) (con y) | yes eq = yes (cong con eq)
  μ-dec {F = F} {i} (con x) (con y) | no neq = no (neq ∘ cong decon)
  
  U-dec : {n : ℕ} {F : Functor n} (G : U n) → Decidable (_≡_ {A = ⟦ G ⟧ (μ F)})
  U-dec (var i  ) x        y         = μ-dec x y
  U-dec (k A dec) x        y         = dec x y
  U-dec  one      x        y         = yes refl
  U-dec (G ⊕ H  ) (inj₁ x) (inj₁ x') with U-dec G x x'
  U-dec (G ⊕ H  ) (inj₁ x) (inj₁ x') | yes eq = yes (cong inj₁ eq)
  U-dec (G ⊕ H  ) (inj₁ x) (inj₁ x') | no neq = no (neq ∘ decong-inj₁)
  U-dec (G ⊕ H  ) (inj₁ x) (inj₂ y ) = no (λ ())
  U-dec (G ⊕ H  ) (inj₂ y) (inj₁ x ) = no (λ ())
  U-dec (G ⊕ H  ) (inj₂ y) (inj₂ y') with U-dec H y y'
  U-dec (G ⊕ H  ) (inj₂ y) (inj₂ y') | yes eq = yes (cong inj₂ eq)
  U-dec (G ⊕ H  ) (inj₂ y) (inj₂ y') | no neq = no (neq ∘ decong-inj₂)
  U-dec (G ⊗ H  ) (x , y ) (x' , y') with U-dec G x x' | U-dec H y y'
  U-dec (G ⊗ H  ) (x , y ) (x' , y') | yes xeq | yes yeq = yes (cong₂ _,_ xeq yeq)
  U-dec (G ⊗ H  ) (x , y ) (x' , y') | yes xeq | no yneq = no (yneq ∘ cong proj₂)
  U-dec (G ⊗ H  ) (x , y ) (x' , y') | no xneq | _       = no (xneq ∘ cong proj₁)
  U-dec (list G ) []       []        = yes refl
  U-dec (list G ) []       (y ∷ ys)  = no (λ ())
  U-dec (list G ) (x ∷ xs) []        = no (λ ())
  U-dec (list G ) (x ∷ xs) (y ∷ ys)  with U-dec G x y | U-dec (list G) xs ys
  U-dec (list G ) (x ∷ xs) (y ∷ ys)  | yes eq | yes eq' = yes (cong₂ _∷_ eq eq')
  U-dec (list G ) (x ∷ xs) (y ∷ ys)  | yes eq | no neq' = no (neq' ∘ cong-tail)
  U-dec (list G ) (x ∷ xs) (y ∷ ys)  | no neq | _       = no (neq  ∘ cong-head)

data Pattern {n : ℕ} (F : Functor n) : U n → Set₁ where
  var   : {G : U n} → Pattern F G
  k     : {G : U n} (x : ⟦ G ⟧ (μ F)) → Pattern F G
  child : {i : Fin n} (pat : Pattern F (F i)) → Pattern F (var i)
  left  : {G H : U n} (pat : Pattern F G) → Pattern F (G ⊕ H)
  right : {G H : U n} (pat : Pattern F H) → Pattern F (G ⊕ H)
  prod  : {G H : U n} (lpat : Pattern F G) (rpat : Pattern F H) → Pattern F (G ⊗ H)
  elem  : {G : U n} (hpat : Pattern F G) (tpat : Pattern F (list G)) → Pattern F (list G)

⟦_⟧ᴾ : {l : Level} {n : ℕ} {F : Functor n} {G : U n} → Pattern F G → (U n → Set l) → Set l
⟦ var  {G}       ⟧ᴾ f = f G
⟦ k x            ⟧ᴾ f = ⊤
⟦ child pat      ⟧ᴾ f = ⟦ pat ⟧ᴾ f
⟦ left pat       ⟧ᴾ f = ⟦ pat ⟧ᴾ f
⟦ right pat      ⟧ᴾ f = ⟦ pat ⟧ᴾ f
⟦ prod lpat rpat ⟧ᴾ f = ⟦ lpat ⟧ᴾ f × ⟦ rpat ⟧ᴾ f
⟦ elem hpat tpat ⟧ᴾ f = ⟦ hpat ⟧ᴾ f × ⟦ tpat ⟧ᴾ f

defaultᴾ : {l : Level} {n : ℕ} {F : Functor n} {G : U n}
           (pat : Pattern F G) (f : U n → Set l) → ((H : U n) → f H) → ⟦ pat ⟧ᴾ f
defaultᴾ (var {G}       ) f g = g G
defaultᴾ (k x           ) f g = tt
defaultᴾ (child pat     ) f g = defaultᴾ pat f g
defaultᴾ (left pat      ) f g = defaultᴾ pat f g
defaultᴾ (right pat     ) f g = defaultᴾ pat f g
defaultᴾ (prod lpat rpat) f g = defaultᴾ lpat f g , defaultᴾ rpat f g
defaultᴾ (elem hpat tpat) f g = defaultᴾ hpat f g , defaultᴾ tpat f g

module PatternMatching {n : ℕ} {F : Functor n} where

  ⟦_⟧ᴾᵁ : {G : U n} → Pattern F G → (U n → U n) → (U n → U n) → U n
  ⟦ var  {G}       ⟧ᴾᵁ f g = f G
  ⟦ k x            ⟧ᴾᵁ f g = one
  ⟦ child pat      ⟧ᴾᵁ f g = ⟦ pat  ⟧ᴾᵁ f g
  ⟦ left pat       ⟧ᴾᵁ f g = ⟦ pat  ⟧ᴾᵁ f g
  ⟦ right pat      ⟧ᴾᵁ f g = ⟦ pat  ⟧ᴾᵁ f g
  ⟦ prod lpat rpat ⟧ᴾᵁ f g = ⟦ lpat ⟧ᴾᵁ f g ⊗ ⟦ rpat ⟧ᴾᵁ f g
  ⟦ elem hpat tpat ⟧ᴾᵁ f g = ⟦ hpat ⟧ᴾᵁ f g ⊗ ⟦ tpat ⟧ᴾᵁ f g

  PatResultU : {G : U n} → Pattern F G → U n
  PatResultU pat = ⟦ pat ⟧ᴾᵁ id id

  PatResult : {G : U n} → Pattern F G → Set
  PatResult pat = ⟦ PatResultU pat ⟧ (μ F)

  deconstruct : {G : U n} (pat : Pattern F G) → ⟦ G ⟧ (μ F) → Par (PatResult pat)
  deconstruct         var              x        = return x
  deconstruct {G = G} (k x'          ) x        with U-dec G x' x
  deconstruct         (k x'          ) x        | yes _ = return tt
  deconstruct         (k x'          ) x        | no  _ = fail
  deconstruct         (child pat     ) (con x)  = deconstruct pat x
  deconstruct         (left pat      ) (inj₁ x) = deconstruct pat x
  deconstruct         (left pat      ) (inj₂ x) = fail
  deconstruct         (right pat     ) (inj₁ x) = fail
  deconstruct         (right pat     ) (inj₂ x) = deconstruct pat x
  deconstruct         (prod lpat rpat) (x , y ) = liftPar₂ _,_ (deconstruct lpat x) (deconstruct rpat y)
  deconstruct         (elem hpat tpat) []       = fail
  deconstruct         (elem hpat tpat) (x ∷ xs) = liftPar₂ _,_ (deconstruct hpat x) (deconstruct tpat xs)

  construct : {G : U n} (pat : Pattern F G) → PatResult pat → ⟦ G ⟧ (μ F)
  construct var              x       = x
  construct (k x'          ) tt      = x'
  construct (child pat     ) x       = con (construct pat x)
  construct (left pat      ) x       = inj₁ (construct pat x)
  construct (right pat     ) x       = inj₂ (construct pat x)
  construct (prod lpat rpat) (x , y) = construct lpat x , construct rpat y
  construct (elem hpat tpat) (x , y) = construct hpat x ∷ construct tpat y

  deconstruct-construct-inverse : {G : U n} (pat : Pattern F G) (x : ⟦ G ⟧ (μ F)) {y : PatResult pat} →
    deconstruct pat x ↦ y → construct pat y ≡ x
  deconstruct-construct-inverse         var              x        (return eq) = sym eq
  deconstruct-construct-inverse {G = G} (k x'          ) x        deconstruct↦ with U-dec G x' x
  deconstruct-construct-inverse         (k x'          ) x        deconstruct↦ | yes eq = eq
  deconstruct-construct-inverse         (k x'          ) x        ()           | no  _
  deconstruct-construct-inverse         (child pat     ) (con x)  deconstruct↦ =
    cong con (deconstruct-construct-inverse pat x deconstruct↦)
  deconstruct-construct-inverse         (left pat      ) (inj₁ x) deconstruct↦ =
    cong inj₁ (deconstruct-construct-inverse pat x deconstruct↦)
  deconstruct-construct-inverse         (left pat      ) (inj₂ y) ()
  deconstruct-construct-inverse         (right pat     ) (inj₁ x) ()
  deconstruct-construct-inverse         (right pat     ) (inj₂ y) deconstruct↦ =
    cong inj₂ (deconstruct-construct-inverse pat y deconstruct↦)
  deconstruct-construct-inverse         (prod lpat rpat) (x , y)  (deconstruct-lpat-x↦ >>=
                                                                   deconstruct-rpat-y↦ >>= return refl) =
    cong₂ _,_ (deconstruct-construct-inverse lpat x deconstruct-lpat-x↦)
              (deconstruct-construct-inverse rpat y deconstruct-rpat-y↦)
  deconstruct-construct-inverse         (elem hpat tpat) []       ()
  deconstruct-construct-inverse         (elem hpat tpat) (x ∷ xs) (deconstruct-epat-x↦ >>=
                                                                   deconstruct-tpat-xs↦ >>= return refl) =
    cong₂ _∷_ (deconstruct-construct-inverse hpat x  deconstruct-epat-x↦ )
              (deconstruct-construct-inverse tpat xs deconstruct-tpat-xs↦)

  construct-deconstruct-inverse : {G : U n} (pat : Pattern F G) (y : PatResult pat) → deconstruct pat (construct pat y) ↦ y
  construct-deconstruct-inverse         var              y       = return refl
  construct-deconstruct-inverse {G = G} (k x           ) y       with U-dec G x x
  construct-deconstruct-inverse {G = G} (k x           ) y       | yes _  = return refl
  construct-deconstruct-inverse {G = G} (k x           ) y       | no neq with neq refl
  construct-deconstruct-inverse {G = G} (k x           ) y       | no neq | ()
  construct-deconstruct-inverse         (child pat     ) y       = construct-deconstruct-inverse pat y
  construct-deconstruct-inverse         (left pat      ) y       = construct-deconstruct-inverse pat y
  construct-deconstruct-inverse         (right pat     ) y       = construct-deconstruct-inverse pat y
  construct-deconstruct-inverse         (prod lpat rpat) (y , z) = construct-deconstruct-inverse lpat y >>=
                                                                   construct-deconstruct-inverse rpat z >>= return refl
  construct-deconstruct-inverse         (elem hpat tpat) (y , z) = construct-deconstruct-inverse hpat y >>=
                                                                   construct-deconstruct-inverse tpat z >>= return refl

  pat-iso : {G : U n} (pat : Pattern F G) → ⟦ G ⟧ (μ F) ≅ PatResult pat
  pat-iso pat = record
    { to   = deconstruct pat
    ; from = return ∘ construct pat
    ; to-from-inverse = return ∘ deconstruct-construct-inverse pat _
    ; from-to-inverse = λ { {_} {._} (return refl) → construct-deconstruct-inverse pat _ } }

open PatternMatching public
