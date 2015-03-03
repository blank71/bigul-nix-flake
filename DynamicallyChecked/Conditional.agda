module DynamicallyChecked.Conditional where

open import Data.Bool
open import Relation.Binary.PropositionalEquality


if-true : {A : Set} {b : Bool} {x y : A} → b ≡ true → (if b then x else y) ≡ x
if-true refl = refl

if-false : {A : Set} {b : Bool} {x y : A} → b ≡ false → (if b then x else y) ≡ y
if-false refl = refl
