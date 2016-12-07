module HoareLogic.Recursion where

open import DynamicallyChecked.Universe
open import DynamicallyChecked.Rearrangement

open import Data.Product
open import Data.Bool
open import Data.Nat
open import Data.List


mutual

  record CoBiGUL∞ {n : ℕ} (F : Functor n) (S V : U n) : Set₁ where
    coinductive
    constructor ♯
    field
      ♭ : CoBiGUL F S V

  data CoBiGUL {n : ℕ} (F : Functor n) : U n → U n → Set₁ where
    delay   : {S V : U n} → CoBiGUL∞ F S V → CoBiGUL F S V
    fail    : {S V : U n} → CoBiGUL F S V
    skip    : {S V : U n} (f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F)) → CoBiGUL F S V
    replace : {S : U n} → CoBiGUL F S S
    prod    : {S V S' V' : U n} (b : CoBiGUL∞ F S V) (b' : CoBiGUL∞ F S' V') → CoBiGUL F (S ⊗ S') (V ⊗ V')
    rearrS  : {S S' V : U n}
              (spat : Pattern F S) (spat' : Pattern F S') (expr : Expr spat spat') (c : CompleteExpr spat spat' expr)
              (b : CoBiGUL∞ F S' V) → CoBiGUL F S V
    rearrV  : {S V V' : U n}
              (vpat : Pattern F V) (vpat' : Pattern F V') (expr : Expr vpat vpat') (c : CompleteExpr vpat vpat' expr)
              (b : CoBiGUL∞ F S V') → CoBiGUL F S V
    dep     : {S V V' : U n} (f : ⟦ V ⟧ (μ F) → ⟦ V' ⟧ (μ F)) (b : CoBiGUL∞ F S V) → CoBiGUL F S (V ⊗ V')
    case    : {S V : U n} (branches : List (CoCaseBranch F S V)) → CoBiGUL F S V
    compose : {A B C : U n} (b : CoBiGUL∞ F A B) (b' : CoBiGUL∞ F B C) → CoBiGUL F A C

  data CoCaseBranchType {n : ℕ} (F : Functor n) (S V : U n) : Set₁ where
    normal   : (b : CoBiGUL∞ F S V) (q : ⟦ S ⟧ (μ F) → Bool) → CoCaseBranchType F S V
    adaptive : (f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)) → CoCaseBranchType F S V

  CoCaseBranch : {n : ℕ} (F : Functor n) (S V : U n) → Set₁
  CoCaseBranch F S V = (⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Bool) × CoCaseBranchType F S V

mutual

  data BiGULᴿ {n : ℕ} (F : Functor n) (S* V* : U n) : U n → U n → Set₁ where
    rec     : BiGULᴿ F S* V* S* V*
    fail    : {S V : U n} → BiGULᴿ F S* V* S V
    skip    : {S V : U n} (f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F)) → BiGULᴿ F S* V* S V
    replace : {S : U n} → BiGULᴿ F S* V* S S
    prod    : {S V S' V' : U n} (b : BiGULᴿ F S* V* S V) (b' : BiGULᴿ F S* V* S' V') → BiGULᴿ F S* V* (S ⊗ S') (V ⊗ V')
    rearrS  : {S S' V : U n}
              (spat : Pattern F S) (spat' : Pattern F S') (expr : Expr spat spat') (c : CompleteExpr spat spat' expr)
              (b : BiGULᴿ F S* V* S' V) → BiGULᴿ F S* V* S V
    rearrV  : {S V V' : U n}
              (vpat : Pattern F V) (vpat' : Pattern F V') (expr : Expr vpat vpat') (c : CompleteExpr vpat vpat' expr)
              (b : BiGULᴿ F S* V* S V') → BiGULᴿ F S* V* S V
    dep     : {S V V' : U n} (f : ⟦ V ⟧ (μ F) → ⟦ V' ⟧ (μ F)) (b : BiGULᴿ F S* V* S V) → BiGULᴿ F S* V* S (V ⊗ V')
    case    : {S V : U n} (branches : List (CaseBranchᴿ F S* V* S V)) → BiGULᴿ F S* V* S V
    compose : {A B C : U n} (b : BiGULᴿ F S* V* A B) (b' : BiGULᴿ F S* V* B C) → BiGULᴿ F S* V* A C

  data CaseBranchTypeᴿ {n : ℕ} (F : Functor n) (S* V* S V : U n) : Set₁ where
    normal   : (b : BiGULᴿ F S* V* S V) (q : ⟦ S ⟧ (μ F) → Bool) → CaseBranchTypeᴿ F S* V* S V
    adaptive : (f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F)) → CaseBranchTypeᴿ F S* V* S V

  CaseBranchᴿ : {n : ℕ} (F : Functor n) (S* V* S V : U n) → Set₁
  CaseBranchᴿ F S* V* S V = (⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Bool) × CaseBranchTypeᴿ F S* V* S V

mutual

  toCoBiGUL∞ : {n : ℕ} {F : Functor n} {S V : U n} → BiGULᴿ F S V S V → CoBiGUL∞ F S V
  toCoBiGUL∞ b = toCoBiGUL∞-worker b b

  toCoBiGUL∞-worker : {n : ℕ} {F : Functor n} {S* V* S V : U n} → BiGULᴿ F S* V* S* V* → BiGULᴿ F S* V* S V → CoBiGUL∞ F S V
  CoBiGUL∞.♭ (toCoBiGUL∞-worker b-orig rec) = delay (toCoBiGUL∞ b-orig)
  CoBiGUL∞.♭ (toCoBiGUL∞-worker b-orig fail) = fail
  CoBiGUL∞.♭ (toCoBiGUL∞-worker b-orig (skip f)) = skip f
  CoBiGUL∞.♭ (toCoBiGUL∞-worker b-orig replace) = replace
  CoBiGUL∞.♭ (toCoBiGUL∞-worker b-orig (prod l r)) = prod (toCoBiGUL∞-worker b-orig l) (toCoBiGUL∞-worker b-orig r)
  CoBiGUL∞.♭ (toCoBiGUL∞-worker b-orig (rearrS spat tpat expr c b)) = rearrS spat tpat expr c (toCoBiGUL∞-worker b-orig b)
  CoBiGUL∞.♭ (toCoBiGUL∞-worker b-orig (rearrV vpat wpat expr c b)) = rearrV vpat wpat expr c (toCoBiGUL∞-worker b-orig b)
  CoBiGUL∞.♭ (toCoBiGUL∞-worker b-orig (dep f b)) = dep f (toCoBiGUL∞-worker b-orig b)
  CoBiGUL∞.♭ (toCoBiGUL∞-worker b-orig (case branches)) = case (toCoBiGUL∞-CoCaseBranch b-orig branches)
  CoBiGUL∞.♭ (toCoBiGUL∞-worker b-orig (compose l r)) = compose (toCoBiGUL∞-worker b-orig l) (toCoBiGUL∞-worker b-orig r)
  
  toCoBiGUL∞-CoCaseBranch : {n : ℕ} {F : Functor n} {S* V* S V : U n} → BiGULᴿ F S* V* S* V* →
                            List (CaseBranchᴿ F S* V* S V) → List (CoCaseBranch F S V)
  toCoBiGUL∞-CoCaseBranch b-orig []                      = []
  toCoBiGUL∞-CoCaseBranch b-orig ((p , normal b q) ∷ bs) = (p , normal (toCoBiGUL∞-worker b-orig b) q) ∷
                                                           toCoBiGUL∞-CoCaseBranch b-orig bs
  toCoBiGUL∞-CoCaseBranch b-orig ((p , adaptive f) ∷ bs) = (p , adaptive f) ∷ toCoBiGUL∞-CoCaseBranch b-orig bs
