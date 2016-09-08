-- The transatlantic corporation example (Section 4).

module BiGUL.TransatlanticCorporation where

open import BiGUL.Utilities
open import BiGUL.Partiality
open import BiGUL.Lens
open import BiGUL.Universe
open import BiGUL.BiGUL
open import BiGUL.ViewRearrangement

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


kℕ : {n : ℕ} → U n
kℕ = k ℕ Data.Nat._≟_

kString : {n : ℕ} → U n
kString = k String Data.String._≟_

Name : {n : ℕ} → U n
Name = kString

Salary : {n : ℕ} → U n
Salary = kℕ

UKLocation : {n : ℕ} → U n
UKLocation = kString

USLocation : {n : ℕ} → U n
USLocation = kString

-- British or American office location
Location : {n : ℕ} → U n
Location = UKLocation ⊕ USLocation

-- name, salary, British or American office location
Employee : {n : ℕ} → U n
Employee = Name ⊗ (Salary ⊗ Location)

-- name, British or American office location
Office : {n : ℕ} → U n
Office = Name ⊗ Location

emptyF : Functor 0
emptyF ()

emptyTEnv : Fin 0 → Set
emptyTEnv ()

relocate-to-UK : BiGUL emptyF (Salary ⊗ Location) (one ⊗ UKLocation)
relocate-to-UK =
  caseS ((return ∘ is-just ∘ isInj₁ ∘ proj₂ , normal   (update (prod var (left  var)) ((, skip) , (, replace)))) ∷
         (const (return true)               , adaptive (λ s → return (⌈ proj₁ s /2⌉ , inj₁ ""))) ∷ [])

relocate-to-US : BiGUL emptyF (Salary ⊗ Location) (one ⊗ USLocation)
relocate-to-US =
  caseS ((return ∘ is-just ∘ isInj₂ ∘ proj₂ , normal   (update (prod var (right var)) ((, skip) , (, replace)))) ∷
         (const (return true)               , adaptive (λ s → return (2 * proj₁ s , inj₂ ""))) ∷ [])

adjust-salary-and-office : BiGUL emptyF (Salary ⊗ Location) Location
adjust-salary-and-office =
  caseV ((return ∘ is-just ∘ isInj₁ , rearr (left  var) (prod (k tt) var) (tt , refl) relocate-to-UK) ∷
         (const (return true)       , rearr (right var) (prod (k tt) var) (tt , refl) relocate-to-US) ∷ [])

relocate-employee : BiGUL emptyF Employee Office
relocate-employee = update (prod var var) ((_ , replace) , (_ , adjust-salary-and-office))

relocate-employees : BiGUL emptyF (list Employee) (list Office)
relocate-employees = align
  (const (return true))
  ((String × ℕ × (String ⊎ String) → String × (String ⊎ String) → Par Bool) ∋
     (λ { (sname , _) (vname , _) → return ⌊ sname Data.String.≟ vname ⌋ }))
  relocate-employee
  ((String × (String ⊎ String) → Par (String × ℕ × (String ⊎ String))) ∋
     (λ { (name , location) → return ("" , 0 , location) }))
  (const (return nothing))

relocate-employees-CompleteExpr : BiGULCompleteExpr emptyF relocate-employees
relocate-employees-CompleteExpr = tt , (return refl , (tt , tt) , tt) , (return refl , (tt , tt) , tt) , tt

employees : ⟦ list Employee ⟧ emptyTEnv
employees = ("Jeremy Gibbons" , 82495 , inj₁ "Oxford University" ) ∷
            ("Meng Wang"      , 13590 , inj₁ "Oxford University" ) ∷
            ("Nate Foster"    , 97000 , inj₂ "Cornell University") ∷
            ("Hugo Pacheco"   , 35000 , inj₂ "Cornell University") ∷ []

locations : ⟦ list Office ⟧ emptyTEnv
locations = ("Jeremy Gibbons" , inj₁ "Oxford University" ) ∷
            ("Meng Wang"      , inj₁ "Oxford University" ) ∷
            ("Nate Foster"    , inj₂ "Cornell University") ∷
            ("Hugo Pacheco"   , inj₂ "Cornell University") ∷ []

locations' : ⟦ list Office ⟧ emptyTEnv
locations' = ("Jeremy Gibbons" , inj₁ "Oxford University" ) ∷
             ("Nate Foster"    , inj₁ "Oxford University" ) ∷
             ("Josh Ko"        , inj₁ "Oxford University" ) ∷
             ("Meng Wang"      , inj₂ "Harvard University") ∷ []

test-get : Maybe (⟦ list Office ⟧ emptyTEnv)
test-get = runPar (Lens.get (interp emptyF relocate-employees relocate-employees-CompleteExpr) employees)

test-put : Maybe (⟦ list Employee ⟧ emptyTEnv)
test-put = runPar (Lens.put (interp emptyF relocate-employees relocate-employees-CompleteExpr) employees locations)

test-put' : Maybe (⟦ list Employee ⟧ emptyTEnv)
test-put' = runPar (Lens.put (interp emptyF relocate-employees relocate-employees-CompleteExpr) employees locations')
