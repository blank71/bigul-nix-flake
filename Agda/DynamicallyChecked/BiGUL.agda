open import DynamicallyChecked.Universe
open import Data.Nat

module DynamicallyChecked.BiGUL {n : ℕ} (F : Functor n) where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens
open import DynamicallyChecked.Rearrangement
open import DynamicallyChecked.Case as Case

open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


mutual

  data BiGUL : U n → U n → Set₁ where
    fail    : {S V : U n} → BiGUL S V
    skip    : {S V : U n} (f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F)) → BiGUL S V
    replace : {S : U n} → BiGUL S S
    prod    : {S V S' V' : U n} (b : BiGUL S V) (b' : BiGUL S' V') → BiGUL (S ⊗ S') (V ⊗ V')
    rearrS  : {S S' V : U n}
              (spat : Pattern F S) (spat' : Pattern F S') (expr : Expr spat spat') (c : CompleteExpr spat spat' expr)
              (b : BiGUL S' V) → BiGUL S V
    rearrV  : {S V V' : U n}
              (vpat : Pattern F V) (vpat' : Pattern F V') (expr : Expr vpat vpat') (c : CompleteExpr vpat vpat' expr)
              (b : BiGUL S V') → BiGUL S V
    dep     : {S V V' : U n} (f : ⟦ V ⟧ (μ F) → ⟦ V' ⟧ (μ F)) (b : BiGUL S V) → BiGUL S (V ⊗ V')
    case    : {S V : U n} (branches : List (CaseBranch S V)) → BiGUL S V
    compose : {A B C : U n} (b : BiGUL A B) (b' : BiGUL B C) → BiGUL A C

  data CaseBranchType (S V : U n) : Set₁ where
    normal   : (b : BiGUL S V) (q : ⟦ S ⟧ (μ F) → Bool) → CaseBranchType S V
    adaptive : (f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)) → CaseBranchType S V

  CaseBranch : (S V : U n) → Set₁
  CaseBranch S V = (⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Bool) × CaseBranchType S V

mutual

  interp : {S V : U n} (b : BiGUL S V) → ⟦ S ⟧ (μ F) ⇆ ⟦ V ⟧ (μ F)
  interp fail                         = iso-lens empty-iso
  interp (skip {V = V} f)             = skip-lens (U-dec V) f
  interp replace                      = iso-lens id-iso
  interp (prod b b')                  = interp b ↕ interp b'
  interp (rearrS spat spat' expr c b) = rearrangement-iso spat spat' expr c ▸ interp b
  interp (rearrV vpat vpat' expr c b) = interp b ◂ sym-iso (rearrangement-iso vpat vpat' expr c)
  interp (dep {V' = V'} f b)          = interp b ◂ sym-iso (dependency-iso f (U-dec V'))
  interp (case {S} {V} branches)      = case-lens (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F)) (interp-CaseBranch branches)
  interp (compose b b')               = interp b ↔ interp b'

  interp-CaseBranch : {S V : U n} (branches : List (CaseBranch S V)) → List (Case.Branch (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F)))
  interp-CaseBranch []                            = []
  interp-CaseBranch ((p , normal b q) ∷ branches) = (p , normal (interp b) q) ∷ interp-CaseBranch branches
  interp-CaseBranch ((p , adaptive u) ∷ branches) = (p , adaptive u) ∷ interp-CaseBranch branches
