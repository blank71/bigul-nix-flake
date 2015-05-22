open import DynamicallyChecked.Universe
open import Data.Nat

module DynamicallyChecked.BiGUL {n : ℕ} (F : Functor n) where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens
open import DynamicallyChecked.SourceUpdate
open import DynamicallyChecked.ViewRearrangement
open import DynamicallyChecked.SourceCase as SourceCase
open import DynamicallyChecked.ViewCase as ViewCase
open import DynamicallyChecked.ListAlignment

open import Data.Product
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


mutual

  data BiGUL : U n → U n → Set₁ where
    fail    : {S V : U n} → BiGUL S V
    skip    : {S : U n} → BiGUL S one
    replace : {S : U n} → BiGUL S S
    update  : {S : U n} → (pat : Pattern F S) (bs : PatBiGUL pat) → BiGUL S (PatBiGULViews pat bs)
    rearr   : {S V V' : U n} → (vpat : Pattern F V) (vpat' : Pattern F V') (expr : Expr vpat vpat')
                               (b : BiGUL S V') → BiGUL S V
    caseS   : {S V : U n} → (branches : List (CaseSBranch S V)) → BiGUL S V
    caseV   : {S V : U n} → (branches : List (CaseVBranch S V)) → BiGUL S V
    align   : {S V : U n} → (source-condition : ⟦ S ⟧ (μ F) → Par Bool) (match? : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Par Bool)
                            (b : BiGUL S V) (create : ⟦ V ⟧ (μ F) → Par (⟦ S ⟧ (μ F)))
                            (conceal : ⟦ S ⟧ (μ F) → Par (Maybe (⟦ S ⟧ (μ F)))) → BiGUL (list S) (list V)

  PatBiGUL : {G : U n} → Pattern F G → Set₁
  PatBiGUL {G} var          = Σ[ H ∈ U n ] BiGUL G H
  PatBiGUL (k x           ) = ⊤
  PatBiGUL (child pat     ) = PatBiGUL pat
  PatBiGUL (left pat      ) = PatBiGUL pat
  PatBiGUL (right pat     ) = PatBiGUL pat
  PatBiGUL (prod lpat rpat) = PatBiGUL lpat × PatBiGUL rpat
  PatBiGUL (elem hpat tpat) = PatBiGUL hpat × PatBiGUL tpat

  PatBiGULViews : {G : U n} (pat : Pattern F G) → PatBiGUL pat → U n
  PatBiGULViews var              (H , _)    = H
  PatBiGULViews (k x           ) tt         = one
  PatBiGULViews (child pat     ) bs         = PatBiGULViews pat bs
  PatBiGULViews (left pat      ) bs         = PatBiGULViews pat bs
  PatBiGULViews (right pat     ) bs         = PatBiGULViews pat bs
  PatBiGULViews (prod lpat rpat) (bs , bs') = PatBiGULViews lpat bs ⊗ PatBiGULViews rpat bs'
  PatBiGULViews (elem hpat tpat) (bs , bs') = PatBiGULViews hpat bs ⊗ PatBiGULViews tpat bs'

  data CaseSBranchType (S V : U n) : Set₁ where
    normal   : BiGUL S V → CaseSBranchType S V
    adaptive : (⟦ S ⟧ (μ F) → Par (⟦ S ⟧ (μ F))) → CaseSBranchType S V

  CaseSBranch : (S V : U n) → Set₁
  CaseSBranch S V = (⟦ S ⟧ (μ F) → Par Bool) × CaseSBranchType S V

  CaseVBranch : (S V : U n) → Set₁
  CaseVBranch S V = Σ[ pat ∈ Pattern F V ] BiGUL S (PatResultU pat)

mutual

  BiGULCompleteExpr : {S V : U n} → BiGUL S V → Set₁
  BiGULCompleteExpr fail = ⊤
  BiGULCompleteExpr skip = ⊤
  BiGULCompleteExpr replace = ⊤
  BiGULCompleteExpr (update pat bs) = PatBiGULCompleteExpr pat bs
  BiGULCompleteExpr (rearr vpat vpat' expr b) = CompleteExpr vpat vpat' expr × BiGULCompleteExpr b
  BiGULCompleteExpr (caseS branches) = CaseSBranchesCompleteExpr branches
  BiGULCompleteExpr (caseV branches) = CaseVBranchesCompleteExpr branches
  BiGULCompleteExpr (align source-condition match? b create conceal) = BiGULCompleteExpr b

  PatBiGULCompleteExpr : {S : U n} (pat : Pattern F S) → PatBiGUL pat → Set₁
  PatBiGULCompleteExpr var              (_ , b)    = BiGULCompleteExpr b
  PatBiGULCompleteExpr (k x)            bs         = ⊤
  PatBiGULCompleteExpr (child pat)      bs         = PatBiGULCompleteExpr pat bs
  PatBiGULCompleteExpr (left  pat)      bs         = PatBiGULCompleteExpr pat bs
  PatBiGULCompleteExpr (right pat)      bs         = PatBiGULCompleteExpr pat bs
  PatBiGULCompleteExpr (prod lpat rpat) (bs , bs') = PatBiGULCompleteExpr lpat bs × PatBiGULCompleteExpr rpat bs'
  PatBiGULCompleteExpr (elem hpat tpat) (bs , bs') = PatBiGULCompleteExpr hpat bs × PatBiGULCompleteExpr tpat bs'

  CaseSBranchesCompleteExpr : {S V : U n} → List (CaseSBranch S V) → Set₁
  CaseSBranchesCompleteExpr []                            = ⊤
  CaseSBranchesCompleteExpr ((p , normal   b) ∷ branches) = BiGULCompleteExpr b × CaseSBranchesCompleteExpr branches
  CaseSBranchesCompleteExpr ((p , adaptive u) ∷ branches) = CaseSBranchesCompleteExpr branches

  CaseVBranchesCompleteExpr : {S V : U n} → List (CaseVBranch S V) → Set₁
  CaseVBranchesCompleteExpr []                     = ⊤
  CaseVBranchesCompleteExpr ((pat , b) ∷ branches) = BiGULCompleteExpr b × CaseVBranchesCompleteExpr branches

mutual

  interp : {S V : U n} (b : BiGUL S V) → BiGULCompleteExpr b → ⟦ S ⟧ (μ F) ⇆ ⟦ V ⟧ (μ F)
  interp fail c = fail-lens
  interp skip c = skip-lens
  interp replace c = iso-lens id-iso
  interp (update pat bs) c = iso-lens (pat-iso pat) ↔ interp-update pat bs c
  interp (rearr vpat vpat' expr b) (c , c') = interp b c' ↔ iso-lens (view-rearrangement-iso vpat vpat' expr c)
  interp (caseS branches) c = caseS-lens _ _ (interp-CaseSBranch branches c)
  interp (caseV branches) c = caseV-lens _ _ (interp-CaseVBranch branches c)
  interp (align source-condition match? b create conceal) c = align-lens source-condition match? (interp b c) create conceal

  interp-update : {S : U n} (pat : Pattern F S) (bs : PatBiGUL pat) → PatBiGULCompleteExpr pat bs →
                  PatResult pat ⇆ ⟦ PatBiGULViews pat bs ⟧ (μ F)
  interp-update var              (_ , b)    c        = interp b c
  interp-update (k x)            bs         c        = iso-lens id-iso
  interp-update (child pat)      bs         c        = interp-update pat bs c
  interp-update (left  pat)      bs         c        = interp-update pat bs c
  interp-update (right pat)      bs         c        = interp-update pat bs c
  interp-update (prod lpat rpat) (bs , bs') (c , c') = interp-update lpat bs c ↕ interp-update rpat bs' c'
  interp-update (elem hpat tpat) (bs , bs') (c , c') = interp-update hpat bs c ↕ interp-update tpat bs' c'

  interp-CaseSBranch : {S V : U n} (branches : List (CaseSBranch S V)) → CaseSBranchesCompleteExpr branches →
                       List (SourceCase.Branch (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F)))
  interp-CaseSBranch []                            c        = []
  interp-CaseSBranch ((p , normal   b) ∷ branches) (c , c') = (p , normal (interp b c)) ∷ interp-CaseSBranch branches c'
  interp-CaseSBranch ((p , adaptive u) ∷ branches) c        = (p , adaptive u) ∷ interp-CaseSBranch branches c
  
  interp-CaseVBranch : {S V : U n} (branches : List (CaseVBranch S V)) → CaseVBranchesCompleteExpr branches →
                       List (ViewCase.Branch (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F)))
  interp-CaseVBranch []                     c        = []
  interp-CaseVBranch ((pat , b) ∷ branches) (c , c') =
    (PatResult pat , interp b c , sym-iso (pat-iso pat)) ∷ interp-CaseVBranch branches c'
