module DynamicallyChecked.CompSeq where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality hiding (_↦_)

open import Data.Product
open import Data.Sum
open import Data.Bool
open import Relation.Binary.PropositionalEquality


infix 0 _↦_ _/↦

mutual

  _↦_ : {A : Set} → Par A → A → Set
  return x         ↦ x' = x ≡ x'
  mx >>= f         ↦ y  = ∃ λ x → (mx ↦ x) × (f x ↦ y)
  fail             ↦ x  = ⊥
  catch mx f my    ↦ y  = (∃ λ x → (mx ↦ x) × (f x ↦ y)) ⊎ ((mx /↦) × (my ↦ y))
  assert b then mx ↦ x  = (b ≡ true) × (mx ↦ x)   

  _/↦ : {A : Set} → Par A → Set
  return x         /↦ = ⊥
  mx >>= f         /↦ = (mx /↦) ⊎ (∃ λ x → (mx ↦ x) × (f x /↦))
  fail             /↦ = ⊤
  catch mx f my    /↦ = (∃ λ x → (mx ↦ x) × (f x /↦)) ⊎ ((mx /↦) × (my /↦))
  assert b then mx /↦ = (b ≡ false) ⊎ ((b ≡ true) × (mx /↦))

record Lens (S V : Set) : Set₁ where
  field
    put  : S → V → Par S
    get  : S → Par V
    PutGet  : {s s' : S} {v : V} → (put s v ↦ s') → (get s' ↦ v)
    GetPut  : {s : S} {v : V} → (get s ↦ v) → (put s v ↦ s)

_⇆_ : Set → Set → Set₁
S ⇆ V = Lens S V

_↔_ : {A B C : Set} → A ⇆ B → B ⇆ C → A ⇆ C
l ↔ r = record
  {  put  = λ a c → Lens.get l a >>= λ b → Lens.put r b c >>= Lens.put l a
  ;  get  = λ a → Lens.get l a >>= Lens.get r
  ;  PutGet  = λ { (b , get-l-a↦b , b' , put-r-b↦b' , put-l-a-b'↦a') →
                   b' , Lens.PutGet l put-l-a-b'↦a' , Lens.PutGet r put-r-b↦b' }
  ;  GetPut  = λ { (b , get-l-a↦b , get-r-b↦c) →
                   b , get-l-a↦b , b , Lens.GetPut r get-r-b↦c , Lens.GetPut l get-l-a↦b } }
