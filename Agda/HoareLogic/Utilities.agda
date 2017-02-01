module HoareLogic.Utilities where

open import Level using (Level)
open import Data.Sum
open import Data.Bool
open import Data.Nat as Nat
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


trueFromWitness : {l : Level} {P : Set l} {d : Dec P} → P → ⌊ d ⌋ ≡ true
trueFromWitness {d = yes _} p = refl
trueFromWitness {d = no ¬p} p with ¬p p
trueFromWitness {d = no ¬p} p | ()

trueToWitness : {l : Level} {P : Set l} {d : Dec P} → ⌊ d ⌋ ≡ true → P
trueToWitness {d = yes p} eq = p
trueToWitness {d = no ¬p} ()

falseFromWitness : {l : Level} {P : Set l} {d : Dec P} → ¬ P → ⌊ d ⌋ ≡ false
falseFromWitness {d = yes p} ¬p with ¬p p
falseFromWitness {d = yes p} ¬p | ()
falseFromWitness {d = no _ } ¬p = refl 

falseToWitness : {l : Level} {P : Set l} {d : Dec P} → ⌊ d ⌋ ≡ false → ¬ P
falseToWitness {d = yes p} ()
falseToWitness {d = no ¬p} eq = ¬p

pred-lemma : {m n : ℕ} → suc m ≡ n → pred n < n
pred-lemma refl = DecTotalOrder.refl Nat.decTotalOrder

pred-inverse-lemma : {n : ℕ} → pred n < n → suc (pred n) ≡ n
pred-inverse-lemma {zero } ()
pred-inverse-lemma {suc n} _ = refl
