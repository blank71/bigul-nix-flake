module DynamicallyChecked.Bookstore where

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
open import Relation.Binary.PropositionalEquality

SBookU : {n : ℕ} → U n
SBookU = k String Data.String._≟_ ⊗ (k String Data.String._≟_ ⊗ (k ℕ Data.Nat._≟_ ⊗ k ℕ Data.Nat._≟_))

VBookU : {n : ℕ} → U n
VBookU = k String Data.String._≟_ ⊗ k ℕ Data.Nat._≟_

emptyF : Functor 0
emptyF ()

emptyTEnv : Fin 0 → Set
emptyTEnv ()

bookstore : BiGUL emptyF (list SBookU) (list VBookU)
bookstore =
  align (const (return true))
        match?
        (rearr (prod var var) (prod var (prod (k tt) (prod (k tt) var))) (inj₁ refl , tt , tt , inj₂ refl)
               (update (prod var (prod var (prod var var)))
                       ((, replace) , ((, skip) , ((, skip) , (, replace))))))
        (const (return ("" , "" , 0 , 0)))
        (const (return nothing))
  where
    match? : ⟦ SBookU ⟧ emptyTEnv → ⟦ VBookU ⟧ emptyTEnv → Par Bool
    match? (stitle , author , year , sprice) (vtitle , vprice) = return (stitle == vtitle)

bookstore-CompleteExpr : BiGULCompleteExpr emptyF bookstore
bookstore-CompleteExpr = (return refl >>= return refl) , tt , tt , tt , tt

sbooks : ⟦ list SBookU ⟧ emptyTEnv
sbooks = ("Harry Potter" , "JK Rowling" , 1997 , 950) ∷ ("The Lord of the Rings" , "JRR Tolkien" , 1954 , 450) ∷ []

vbooks' : ⟦ list VBookU ⟧ emptyTEnv
vbooks' = ("Harry Potter" , 850) ∷ ("The Hitchhiker's Guide to the Galaxy" , 650) ∷ []

vbooks : ⟦ list VBookU ⟧ emptyTEnv
vbooks = ("Harry Potter" , 950) ∷ ("The Lord of the Rings" , 450) ∷ []

test-get : Maybe (⟦ list VBookU ⟧ emptyTEnv)
test-get = runPar (Lens.get (interp emptyF bookstore bookstore-CompleteExpr) sbooks)

test-put : Maybe (⟦ list SBookU ⟧ emptyTEnv)
test-put = runPar (Lens.put (interp emptyF bookstore bookstore-CompleteExpr) sbooks vbooks)

test-put' : Maybe (⟦ list SBookU ⟧ emptyTEnv)
test-put' = runPar (Lens.put (interp emptyF bookstore bookstore-CompleteExpr) sbooks vbooks')
