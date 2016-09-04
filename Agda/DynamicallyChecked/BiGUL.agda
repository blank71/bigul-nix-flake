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
              (spat : Pattern F S) (spat' : Pattern F S') (expr : Expr spat spat') (b : BiGUL S' V) → BiGUL S V
    rearrV  : {S V V' : U n}
              (vpat : Pattern F V) (vpat' : Pattern F V') (expr : Expr vpat vpat') (b : BiGUL S V') → BiGUL S V
    dep     : {S V V' : U n} (f : ⟦ V ⟧ (μ F) → ⟦ V' ⟧ (μ F)) (b : BiGUL S V) → BiGUL S (V ⊗ V')
    case    : {S V : U n} (branches : List (CaseBranch S V)) → BiGUL S V
    compose : {A B C : U n} (b : BiGUL A B) (b' : BiGUL B C) → BiGUL A C

  data CaseBranchType (S V : U n) : Set₁ where
    normal   : (b : BiGUL S V) (q : ⟦ S ⟧ (μ F) → Bool) → CaseBranchType S V
    adaptive : (f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)) → CaseBranchType S V

  CaseBranch : (S V : U n) → Set₁
  CaseBranch S V = (⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Bool) × CaseBranchType S V

mutual

  BiGULCompleteExpr : {S V : U n} → BiGUL S V → Set₁
  BiGULCompleteExpr fail                       = ⊤
  BiGULCompleteExpr (skip f)                   = ⊤
  BiGULCompleteExpr replace                    = ⊤
  BiGULCompleteExpr (prod b b')                = BiGULCompleteExpr b × BiGULCompleteExpr b'
  BiGULCompleteExpr (rearrS spat spat' expr b) = BiGULCompleteExpr b
  BiGULCompleteExpr (rearrV vpat vpat' expr b) = CompleteExpr vpat vpat' expr × BiGULCompleteExpr b
  BiGULCompleteExpr (dep f b)                  = BiGULCompleteExpr b
  BiGULCompleteExpr (case branches)            = CaseBranchesCompleteExpr  branches
  BiGULCompleteExpr (compose b b')             = BiGULCompleteExpr b × BiGULCompleteExpr b'

  CaseBranchesCompleteExpr : {S V : U n} → List (CaseBranch S V) → Set₁
  CaseBranchesCompleteExpr []                            = ⊤
  CaseBranchesCompleteExpr ((p , normal b q) ∷ branches) = BiGULCompleteExpr b × CaseBranchesCompleteExpr branches
  CaseBranchesCompleteExpr ((p , adaptive u) ∷ branches) = CaseBranchesCompleteExpr branches

mutual

  interp : {S V : U n} (b : BiGUL S V) → BiGULCompleteExpr b → ⟦ S ⟧ (μ F) ⇆ ⟦ V ⟧ (μ F)
  interp fail                       c        = iso-lens empty-iso
  interp (skip {V = V} f)           c        = skip-lens (U-dec V) f
  interp replace                    c        = iso-lens id-iso
  interp (prod b b')                (c , c') = interp b c ↕ interp b' c' 
  interp (rearrS spat spat' expr b) c        = source-rearrangement-lens spat spat' expr ↔ interp b c
  interp (rearrV vpat vpat' expr b) (c , c') = interp b c' ◁ sym-iso (view-rearrangement-iso vpat vpat' expr c)
  interp (dep {V' = V'} f b)        c        = interp b c ◁ sym-iso (dependency-iso f (U-dec V'))
  interp (case {S} {V} branches)    c        = case-lens (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F)) (interp-CaseBranch branches c)
  interp (compose b b')             (c , c') = interp b c ↔ interp b' c'

  interp-CaseBranch : {S V : U n} (branches : List (CaseBranch S V)) → CaseBranchesCompleteExpr branches →
                      List (Case.Branch (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F)))
  interp-CaseBranch []                            c        = []
  interp-CaseBranch ((p , normal b q) ∷ branches) (c , c') = (p , normal (interp b c) q) ∷ interp-CaseBranch branches c'
  interp-CaseBranch ((p , adaptive u) ∷ branches) c        = (p , adaptive u) ∷ interp-CaseBranch branches c
