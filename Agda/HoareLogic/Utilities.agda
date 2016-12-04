module HoareLogic.Utilities where

open import Level
open import Data.Sum
open import Data.Bool
open import Relation.Nullary
open import Relation.Nullary.Decidable
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
