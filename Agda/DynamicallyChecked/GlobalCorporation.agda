module DynamicallyChecked.GlobalCorporation where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens
open import DynamicallyChecked.Universe
open import DynamicallyChecked.BiGUL
open import DynamicallyChecked.ViewRearrangement

open import Function
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Data.Fin
open import Data.List
open import Data.String
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality


kString : {n : ℕ} → U n
kString = k String Data.String._≟_

-- name, salary, British or American office location
EmployeeU : {n : ℕ} → U n
EmployeeU = kString ⊗ (k ℕ Data.Nat._≟_ ⊗ (kString ⊕ kString))

-- name, British or American office location
LocationU : {n : ℕ} → U n
LocationU = kString ⊗ (kString ⊕ kString)

emptyF : Functor 0
emptyF ()

emptyTEnv : Fin 0 → Set
emptyTEnv ()

inBritain : ℕ × (String ⊎ String) → Par Bool
inBritain (_ , inj₁ _) = return true
inBritain (_ , inj₂ _) = return false

inAmerica : ℕ × (String ⊎ String) → Par Bool
inAmerica (_ , inj₁ _) = return false
inAmerica (_ , inj₂ _) = return true

globalCorporation : BiGUL emptyF (list EmployeeU) (list LocationU)
globalCorporation =
  align (const (return true))
        ((String × ℕ × (String ⊎ String) → String × (String ⊎ String) → Par Bool) ∋
           (λ { (sname , _) (vname , _) → return ⌊ sname Data.String.≟ vname ⌋ }))
        (rearr (prod var var) (prod var (prod (k tt) var)) (inj₁ refl , tt , inj₂ refl)
           (update (prod var var)
              ((, replace) ,
               (, caseV ((prod var (left  var) ,
                            caseS ((inBritain ,
                                      normal (update (prod var (left  var)) ((, skip) , (, replace)))) ∷
                                   (inAmerica ,
                                      adaptive (λ s → return (⌈ proj₁ s /2⌉ , inj₁ ""))) ∷ [])) ∷
                         (prod var (right var) ,
                            caseS ((inBritain ,
                                      adaptive (λ s → return (2 * proj₁ s , inj₂ ""))) ∷
                                   (inAmerica ,
                                      normal (update (prod var (right var)) ((, skip) , (, replace)))) ∷ [])) ∷ [])))))
        ((String × (String ⊎ String) → Par (String × ℕ × (String ⊎ String))) ∋
           (λ { (name , location) → return (name , 0 , location) }))
        (const (return nothing))

globalCorporation-CompleteExpr : BiGULCompleteExpr emptyF globalCorporation
globalCorporation-CompleteExpr = (return refl >>= return refl) ,
                                   tt , ((tt , tt) , tt) , ((tt , tt) , tt) , tt

employees : ⟦ list EmployeeU ⟧ emptyTEnv
employees = ("Jeremy Gibbons" , 82495 , inj₁ "Oxford University" ) ∷
            ("Meng Wang"      , 13590 , inj₁ "Oxford University" ) ∷
            ("Nate Foster"    , 97000 , inj₂ "Cornell University") ∷
            ("Hugo Pacheco"   , 35000 , inj₂ "Cornell University") ∷ []

locations : ⟦ list LocationU ⟧ emptyTEnv
locations = ("Jeremy Gibbons" , inj₁ "Oxford University" ) ∷
            ("Meng Wang"      , inj₁ "Oxford University" ) ∷
            ("Nate Foster"    , inj₂ "Cornell University") ∷
            ("Hugo Pacheco"   , inj₂ "Cornell University") ∷ []

locations' : ⟦ list LocationU ⟧ emptyTEnv
locations' = ("Jeremy Gibbons" , inj₁ "Oxford University" ) ∷
             ("Nate Foster"    , inj₁ "Oxford University" ) ∷
             ("Josh Ko"        , inj₁ "Oxford University" ) ∷
             ("Meng Wang"      , inj₂ "Harvard University") ∷ []

test-get : Maybe (⟦ list LocationU ⟧ emptyTEnv)
test-get = runPar (Lens.get (interp emptyF globalCorporation globalCorporation-CompleteExpr) employees)

test-put : Maybe (⟦ list EmployeeU ⟧ emptyTEnv)
test-put = runPar (Lens.put (interp emptyF globalCorporation globalCorporation-CompleteExpr) employees locations)

test-put' : Maybe (⟦ list EmployeeU ⟧ emptyTEnv)
test-put' = runPar (Lens.put (interp emptyF globalCorporation globalCorporation-CompleteExpr) employees locations')
