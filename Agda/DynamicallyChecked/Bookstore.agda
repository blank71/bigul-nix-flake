module DynamicallyChecked.Bookstore where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens
open import DynamicallyChecked.Universe
open import DynamicallyChecked.BiGUL
open import DynamicallyChecked.Rearrangement

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

-- title, author, year, price, in stock
SBookU : {n : ℕ} → U n
SBookU = kString ⊗ (kString ⊗ (k ℕ Data.Nat._≟_ ⊗ (k ℕ Data.Nat._≟_ ⊗ k Bool Data.Bool._≟_)))

-- title, price
VBookU : {n : ℕ} → U n
VBookU = kString ⊗ k ℕ Data.Nat._≟_

emptyF : Functor 0
emptyF ()

emptyTEnv : Fin 0 → Set
emptyTEnv ()

bookstore : BiGUL emptyF (list SBookU) (list VBookU)
bookstore =
  align ((String × String × ℕ × ℕ × Bool → Par Bool) ∋
           (λ { (_ , _ , year , _ , instock) → return (⌊ year Data.Nat.≟ 2015 ⌋ ∧ instock) }))
        ((String × String × ℕ × ℕ × Bool → String × ℕ → Par Bool) ∋
           (λ { (stitle , _) (vtitle , _) → return (stitle == vtitle) }))
        (rearrV (prod var var) (prod var (prod (k tt) (prod (k tt) (prod var (k tt)))))
                (inj₁ refl , tt , tt , inj₂ refl , tt)
                (update (prod var (prod var (prod var (prod var var))))
                        ((, replace) , (, skip) , (, skip) , (, replace) , (, skip))))
        (const (return ("" , "(to be updated)" , 2015 , 0 , true)))
        (λ { (title , author , year , price , instock) → return (just (title , author , year , price , false)) })

bookstore-CompleteExpr : BiGULCompleteExpr emptyF bookstore
bookstore-CompleteExpr = (return refl >>= return refl) , tt , tt , tt , tt , tt

sbooks : ⟦ list SBookU ⟧ emptyTEnv
sbooks = ("Harry Potter" , "JK Rowling" , 2015 , 950 , true) ∷ ("The Lord of the Rings" , "JRR Tolkien" , 1954 , 450 , true) ∷ ("The Swift Programming Language" , "Apple, Inc" , 2015 , 650 , false) ∷ []

vbooks' : ⟦ list VBookU ⟧ emptyTEnv
vbooks' = ("Harry Potter" , 1850) ∷ ("The Hitchhiker's Guide to the Galaxy" , 550) ∷ []

vbooks'' : ⟦ list VBookU ⟧ emptyTEnv
vbooks'' = []

vbooks : ⟦ list VBookU ⟧ emptyTEnv
vbooks = ("Harry Potter" , 1950) ∷ []

test-get : Maybe (⟦ list VBookU ⟧ emptyTEnv)
test-get = runPar (Lens.get (interp emptyF bookstore bookstore-CompleteExpr) sbooks)

test-put : Maybe (⟦ list SBookU ⟧ emptyTEnv)
test-put = runPar (Lens.put (interp emptyF bookstore bookstore-CompleteExpr) sbooks vbooks)

test-put' : Maybe (⟦ list SBookU ⟧ emptyTEnv)
test-put' = runPar (Lens.put (interp emptyF bookstore bookstore-CompleteExpr) sbooks vbooks')

test-put'' : Maybe (⟦ list SBookU ⟧ emptyTEnv)
test-put'' = runPar (Lens.put (interp emptyF bookstore bookstore-CompleteExpr) sbooks vbooks'')
