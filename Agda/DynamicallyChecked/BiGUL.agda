open import DynamicallyChecked.Universe
open import Data.Nat

module DynamicallyChecked.BiGUL where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens
open import DynamicallyChecked.Rearrangement
open import DynamicallyChecked.Case as Case

open import Level
open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


mutual

  data BiGUL {n : ℕ} (F : Functor n) : U n → U n → Set₁ where
    fail    : {S V : U n} → BiGUL F S V
    skip    : {S V : U n} (f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F)) → BiGUL F S V
    replace : {S : U n} → BiGUL F S S
    prod    : {S V S' V' : U n} (b : BiGUL F S V) (b' : BiGUL F S' V') → BiGUL F (S ⊗ S') (V ⊗ V')
    rearrS  : {S S' V : U n}
              (spat : Pattern F S) (spat' : Pattern F S') (expr : Expr spat spat') (c : CompleteExpr spat spat' expr)
              (b : BiGUL F S' V) → BiGUL F S V
    rearrV  : {S V V' : U n}
              (vpat : Pattern F V) (vpat' : Pattern F V') (expr : Expr vpat vpat') (c : CompleteExpr vpat vpat' expr)
              (b : BiGUL F S V') → BiGUL F S V
    case    : {S V : U n} (branches : List (CaseBranch F S V)) → BiGUL F S V

  data CaseBranchType {n : ℕ} (F : Functor n) (S V : U n) : Set₁ where
    normal   : (b : BiGUL F S V) (q : ⟦ S ⟧ (μ F) → Bool) → CaseBranchType F S V
    adaptive : (f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)) → CaseBranchType F S V

  CaseBranch : {n : ℕ} (F : Functor n) (S V : U n) → Set₁
  CaseBranch F S V = (⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Bool) × CaseBranchType F S V

elimCaseBranchType : {n : ℕ} {F : Functor n} {S V : U n} {l : Level} {A : Set l} →
                     (BiGUL F S V → (⟦ S ⟧ (μ F) → Bool) → A) → ((⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)) → A) →
                     CaseBranchType F S V → A
elimCaseBranchType n a (normal b q) = n b q
elimCaseBranchType n a (adaptive f) = a f

mutual

  interp : {n : ℕ} {F : Functor n} {S V : U n} (b : BiGUL F S V) → ⟦ S ⟧ (μ F) ⇆ ⟦ V ⟧ (μ F)
  interp         fail                         = iso-lens empty-iso
  interp         (skip {V = V} f)             = skip-lens (U-dec V) f
  interp         replace                      = iso-lens id-iso
  interp         (prod b b')                  = interp b ↕ interp b'
  interp         (rearrS spat spat' expr c b) = rearrangement-iso spat spat' expr c ▸ interp b
  interp         (rearrV vpat vpat' expr c b) = interp b ◂ sym-iso (rearrangement-iso vpat vpat' expr c)
  interp {F = F} (case {S} {V} branches)      = case-lens (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F)) (interp-CaseBranch branches)

  interp-CaseBranch : {n : ℕ} {F : Functor n} {S V : U n} →
                      List (CaseBranch F S V) → List (Case.Branch (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F)))
  interp-CaseBranch []                            = []
  interp-CaseBranch ((p , normal b q) ∷ branches) = (p , normal (interp b) q) ∷ interp-CaseBranch branches
  interp-CaseBranch ((p , adaptive u) ∷ branches) = (p , adaptive u) ∷ interp-CaseBranch branches
