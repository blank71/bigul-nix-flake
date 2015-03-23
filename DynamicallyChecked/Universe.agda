module DynamicallyChecked.Universe where

open import DynamicallyChecked.Partiality

open import Function using (_∘_; _∋_)
open import Data.Unit
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
  _⊕_  : (F G : U n) → U n
  _⊗_  : (F G : U n) → U n
  list : (F : U n)   → U n

⟦_⟧ : {n : ℕ} → U n → (Fin n → Set) → Set
⟦ var  i  ⟧ Xs = Xs i
⟦ k A dec ⟧ Xs = A
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
  μ-dec {F = F} {i} (con x) (con y) | yes eq  = yes (cong con eq)
  μ-dec {F = F} {i} (con x) (con y) | no neq = no (neq ∘ cong decon)
  
  U-dec : {n : ℕ} {F : Functor n} (G : U n) → Decidable (_≡_ {A = ⟦ G ⟧ (μ F)})
  U-dec (var i  ) x        y         = μ-dec x y
  U-dec (k A dec) x        y         = dec x y
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

data Pattern {n : ℕ} (F : Functor n) : U n → Set where
  var   : {G : U n} → Pattern F G
  const : {G : U n} (x : ⟦ G ⟧ (μ F)) → Pattern F G
  child : {i : Fin n} (pat : Pattern F (F i)) → Pattern F (var i)
  left  : {G H : U n} (pat : Pattern F G) → Pattern F (G ⊕ H)
  right : {G H : U n} (pat : Pattern F H) → Pattern F (G ⊕ H)
  prod  : {G H : U n} (lpat : Pattern F G) (rpat : Pattern F H) → Pattern F (G ⊗ H)
  list  : {G : U n} (pats : List (Pattern F G)) → Pattern F (list G)

mutual

  ⟦_⟧ᴾ : {n : ℕ} {F : Functor n} {G : U n} → Pattern F G → Set
  ⟦_⟧ᴾ {F = F} {G} var = ⟦ G ⟧ (μ F)
  ⟦ const x        ⟧ᴾ = ⊤
  ⟦ child pat      ⟧ᴾ = ⟦ pat ⟧ᴾ
  ⟦ left pat       ⟧ᴾ = ⟦ pat ⟧ᴾ
  ⟦ right pat      ⟧ᴾ = ⟦ pat ⟧ᴾ
  ⟦ prod lpat rpat ⟧ᴾ = ⟦ lpat ⟧ᴾ × ⟦ rpat ⟧ᴾ
  ⟦ list pats      ⟧ᴾ = ⟦ pats ⟧ᴾˢ

  ⟦_⟧ᴾˢ : {n : ℕ} {F : Functor n} {G : U n} → List (Pattern F G) → Set
  ⟦_⟧ᴾˢ {F = F} {G} [] = List (⟦ G ⟧ (μ F))
  ⟦ pat ∷ pats ⟧ᴾˢ = ⟦ pat ⟧ᴾ × ⟦ pats ⟧ᴾˢ

mutual

  deconstruct : {n : ℕ} {F : Functor n} {G : U n} (pat : Pattern F G) → ⟦ G ⟧ (μ F) → Par ⟦ pat ⟧ᴾ
  deconstruct         var              x        = return x
  deconstruct {G = G} (const x'      ) x        with U-dec G x' x
  deconstruct         (const x'      ) x        | yes _ = return tt
  deconstruct         (const x'      ) x        | no  _ = fail
  deconstruct         (child pat     ) (con x)  = deconstruct pat x
  deconstruct         (left pat      ) (inj₁ x) = deconstruct pat x
  deconstruct         (left pat      ) (inj₂ x) = fail
  deconstruct         (right pat     ) (inj₁ x) = fail
  deconstruct         (right pat     ) (inj₂ x) = deconstruct pat x
  deconstruct         (prod lpat rpat) (x , y ) = liftPar₂ _,_ (deconstruct lpat x) (deconstruct rpat y)
  deconstruct         (list pats     ) xs       = deconstruct-list pats xs

  deconstruct-list : {n : ℕ} {F : Functor n} {G : U n} (pats : List (Pattern F G)) → List (⟦ G ⟧ (μ F)) → Par ⟦ pats ⟧ᴾˢ
  deconstruct-list []           xs       = return xs
  deconstruct-list (pat ∷ pats) []       = fail
  deconstruct-list (pat ∷ pats) (x ∷ xs) = liftPar₂ _,_ (deconstruct pat x) (deconstruct-list pats xs)

mutual

  construct : {n : ℕ} {F : Functor n} {G : U n} (pat : Pattern F G) → ⟦ pat ⟧ᴾ → ⟦ G ⟧ (μ F)
  construct var              x       = x
  construct (const x'      ) tt      = x'
  construct (child pat     ) x       = con (construct pat x)
  construct (left pat      ) x       = inj₁ (construct pat x)
  construct (right pat     ) x       = inj₂ (construct pat x)
  construct (prod lpat rpat) (x , y) = construct lpat x , construct rpat y
  construct (list pats     ) xs      = construct-list pats xs

  construct-list : {n : ℕ} {F : Functor n} {G : U n} (pats : List (Pattern F G)) → ⟦ pats ⟧ᴾˢ → List (⟦ G ⟧ (μ F))
  construct-list []           xs       = xs
  construct-list (pat ∷ pats) (x , xs) = construct pat x ∷ construct-list pats xs

mutual

  deconstruct-construct-inverse :
    {n : ℕ} {F : Functor n} {G : U n} (pat : Pattern F G) (x : ⟦ G ⟧ (μ F)) {y : ⟦ pat ⟧ᴾ} → deconstruct pat x ↦ y → construct pat y ≡ x
  deconstruct-construct-inverse         var              x        (return eq) = sym eq
  deconstruct-construct-inverse {G = G} (const x'      ) x        deconstruct↦ with U-dec G x' x
  deconstruct-construct-inverse         (const x'      ) x        deconstruct↦ | yes eq = eq
  deconstruct-construct-inverse         (const x'      ) x        ()           | no  _
  deconstruct-construct-inverse         (child pat     ) (con x)  deconstruct↦ = cong con (deconstruct-construct-inverse pat x deconstruct↦)
  deconstruct-construct-inverse         (left pat      ) (inj₁ x) deconstruct↦ = cong inj₁ (deconstruct-construct-inverse pat x deconstruct↦)
  deconstruct-construct-inverse         (left pat      ) (inj₂ y) ()
  deconstruct-construct-inverse         (right pat     ) (inj₁ x) ()
  deconstruct-construct-inverse         (right pat     ) (inj₂ y) deconstruct↦ = cong inj₂ (deconstruct-construct-inverse pat y deconstruct↦)
  deconstruct-construct-inverse         (prod lpat rpat) (x , y)  (deconstruct-lpat-x↦ >>= deconstruct-rpat-y↦ >>= return refl) =
    cong₂ _,_ (deconstruct-construct-inverse lpat x deconstruct-lpat-x↦) (deconstruct-construct-inverse rpat y deconstruct-rpat-y↦)
  deconstruct-construct-inverse         (list pats     ) xs       deconstruct↦ = deconstruct-construct-inverse-list pats xs deconstruct↦

  deconstruct-construct-inverse-list :
    {n : ℕ} {F : Functor n} {G : U n} (pats : List (Pattern F G)) (xs : List (⟦ G ⟧ (μ F))) {y : ⟦ pats ⟧ᴾˢ} →
    deconstruct-list pats xs ↦ y → construct-list pats y ≡ xs
  deconstruct-construct-inverse-list []           xs       (return eq)       = sym eq
  deconstruct-construct-inverse-list (pat ∷ pats) []       ()
  deconstruct-construct-inverse-list (pat ∷ pats) (x ∷ xs) (deconstruct↦ >>= deconstruct-list↦ >>= return refl) =
    cong₂ _∷_ (deconstruct-construct-inverse pat x deconstruct↦) (deconstruct-construct-inverse-list pats xs deconstruct-list↦)

mutual

  construct-deconstruct-inverse :
    {n : ℕ} {F : Functor n} {G : U n} (pat : Pattern F G) (y : ⟦ pat ⟧ᴾ) → deconstruct pat (construct pat y) ↦ y
  construct-deconstruct-inverse         var              y       = return refl
  construct-deconstruct-inverse {G = G} (const x       ) y       with U-dec G x x
  construct-deconstruct-inverse {G = G} (const x       ) y       | yes _  = return refl
  construct-deconstruct-inverse {G = G} (const x       ) y       | no neq with neq refl
  construct-deconstruct-inverse {G = G} (const x       ) y       | no neq | ()
  construct-deconstruct-inverse         (child pat     ) y       = construct-deconstruct-inverse pat y
  construct-deconstruct-inverse         (left pat      ) y       = construct-deconstruct-inverse pat y
  construct-deconstruct-inverse         (right pat     ) y       = construct-deconstruct-inverse pat y
  construct-deconstruct-inverse         (prod lpat rpat) (y , z) = construct-deconstruct-inverse lpat y >>=
                                                                   construct-deconstruct-inverse rpat z >>= return refl
  construct-deconstruct-inverse         (list pats     ) y       = construct-deconstruct-inverse-list pats y

  construct-deconstruct-inverse-list :
    {n : ℕ} {F : Functor n} {G : U n} (pats : List (Pattern F G)) (y : ⟦ pats ⟧ᴾˢ) → deconstruct-list pats (construct-list pats y) ↦ y
  construct-deconstruct-inverse-list []           y       = return refl
  construct-deconstruct-inverse-list (pat ∷ pats) (y , z) = construct-deconstruct-inverse pat y >>=
                                                            construct-deconstruct-inverse-list pats z >>= return refl

pat-iso : {n : ℕ} {F : Functor n} {G : U n} (pat : Pattern F G) → ⟦ G ⟧ (μ F) ≅ ⟦ pat ⟧ᴾ
pat-iso pat = record
  { to   = deconstruct pat
  ; from = return ∘ construct pat
  ; to-from-inverse = return ∘ deconstruct-construct-inverse pat _
  ; from-to-inverse = λ { {_} {._} (return refl) → construct-deconstruct-inverse pat _ } }
