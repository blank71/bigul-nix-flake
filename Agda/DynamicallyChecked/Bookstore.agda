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
open import Data.Bool as Bool
open import Data.Maybe as Maybe
open import Data.Nat as Nat
open import Data.Fin
open import Data.List
open import Data.String as String
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality


kString : {n : ℕ} → U n
kString = k String String._≟_

-- title, author, year, price, in stock
SBookU : {n : ℕ} → U n
SBookU = kString ⊗ (kString ⊗ (k ℕ Nat._≟_ ⊗ (k ℕ Nat._≟_ ⊗ k Bool Bool._≟_)))

-- title, price
VBookU : {n : ℕ} → U n
VBookU = kString ⊗ k ℕ Nat._≟_

BookstoreF : Functor 2
BookstoreF zero       = one ⊕ (SBookU ⊗ var zero)
BookstoreF (suc zero) = one ⊕ (VBookU ⊗ var (suc zero))
BookstoreF (suc (suc ()))

concealPrefix : μ BookstoreF zero → μ BookstoreF zero
concealPrefix (con (inj₁ tt)) = con (inj₁ tt)
concealPrefix (con (inj₂ ((title , author , year , price , instock) , ss))) with ⌊ year Nat.≟ 2015 ⌋ ∧ instock
... | true  = (con (inj₂ ((title , author , year , price , false) , concealPrefix ss)))
... | false = (con (inj₂ ((title , author , year , price , instock) , ss)))

findFirstMatch : String → μ BookstoreF zero → Maybe (⟦ SBookU ⟧ (μ BookstoreF) × μ BookstoreF zero)
findFirstMatch vtitle (con (inj₁ tt)) = nothing
findFirstMatch vtitle (con (inj₂ ((stitle , author , year , price , instock) , ss)))
    with ⌊ year Nat.≟ 2015 ⌋ ∧ instock ∧ (vtitle == stitle)
... | true  = just ((stitle , author , year , price , instock) , ss) 
... | false = Maybe.map (λ { (s' , ss') → (s' , con (inj₂ ((stitle , author , year , price , instock) , ss'))) })
                        (findFirstMatch vtitle ss) 

bookstoreB : BiGUL BookstoreF (var zero) (var (suc zero)) → BiGUL BookstoreF (var zero) (var (suc zero))
bookstoreB rec = case
  (((λ { (con (inj₁ tt)) (con (inj₁ tt)) → true; _ _ → false }) ,
      normal
        (rearrV (con (left (k tt))) (k {G = one} tt) tt (return refl) (skip (const tt)))
        (λ { (con (inj₁ tt)) → true; _ → false })) ∷
   ((λ { (con (inj₂ ((stitle , _) , _))) (con (inj₂ ((vtitle , _) , _))) → stitle == vtitle; _ _ → false }) ,
      normal
        (rearrS (con (right (prod (prod var (prod var (prod var (prod var var)))) var)))
                (prod (prod (prod var var) var) (prod var (prod var var)))
                (((inj₁ (inj₁ refl) , inj₁ (inj₂ (inj₂ (inj₂ (inj₁ refl))))) , inj₂ refl) ,
                 inj₁ (inj₂ (inj₁ refl)) , inj₁ (inj₂ (inj₂ (inj₁ refl))) , inj₁ (inj₂ (inj₂ (inj₂ (inj₂ refl)))))
                ((return refl >>= return refl >>= return refl >>= return refl >>= return refl) >>= return refl)
           (rearrV (con (right var)) (prod var (k {G = one} tt)) (refl , tt) (return refl)
              (prod (prod replace rec) (skip (const tt)))))
        (λ { (con (inj₂ ((_ , _ , year , _ , instock) , _))) → ⌊ year Nat.≟ 2015 ⌋ ∧ instock; _ → false })) ∷
   ((λ { (con (inj₂ ((_ , _ , year , _ , instock) , _))) (con (inj₁ tt)) → ⌊ year Nat.≟ 2015 ⌋ ∧ instock; _ _ → false }) ,
      adaptive
        (λ ss _ → concealPrefix ss)) ∷
   ((λ { (con (inj₂ ((_ , _ , year , _ , instock) , _))) _ → not (⌊ year Nat.≟ 2015 ⌋ ∧ instock); _ _ → false }) ,
      normal
        (rearrS (con (right (prod var var))) (prod var var) (inj₂ refl , inj₁ refl) (return refl >>= return refl)
           (rearrV var (prod var (k {G = one} tt)) (refl , tt) (return refl) (prod rec (skip (const tt)))))
        (λ { (con (inj₂ ((_ , _ , year , _ , instock) , _))) → not (⌊ year Nat.≟ 2015 ⌋ ∧ instock); _ → false })) ∷
   ((λ { ss (con (inj₂ ((vtitle , _) , _))) → is-just (findFirstMatch vtitle ss) ; _ _ → false }) ,
      adaptive
        (λ { ss (con (inj₂ ((vtitle , _) , _))) →
             case (findFirstMatch vtitle ss) of
               λ { (just (s' , ss')) → con (inj₂ (s' , ss')); _ → con (inj₁ tt) }; _ _ → con (inj₁ tt) })) ∷
   ((λ _ _ → true) ,
      adaptive
        ((λ { ss (con (inj₂ ((vtitle , _) , _))) → con (inj₂ ((vtitle , "(to be updated)" , 2015 , 0 , true) , ss))
            ; _ _ → con (inj₁ tt) }))) ∷ [])

-- non-terminating
bookstore : BiGUL BookstoreF (var zero) (var (suc zero))
bookstore = fix bookstoreB

sbooks : μ BookstoreF zero
sbooks = con (inj₂ (("Harry Potter"                   , "JK Rowling"  , 2015 , 950 , true ) ,
         con (inj₂ (("The Lord of the Rings"          , "JRR Tolkien" , 1954 , 450 , true ) ,
         con (inj₂ (("The Swift Programming Language" , "Apple, Inc"  , 2015 , 650 , false) ,
         con (inj₁ tt)))))))

vbooks' : μ BookstoreF (suc zero)
vbooks' = con (inj₂ (("Harry Potter"                         , 1850) ,
          con (inj₂ (("The Hitchhiker's Guide to the Galaxy" ,  550) ,
          con (inj₁ tt)))))

vbooks'' : μ BookstoreF (suc zero)
vbooks'' = con (inj₁ tt)

vbooks : μ BookstoreF (suc zero)
vbooks = con (inj₂ (("Harry Potter" , 1950) ,
         con (inj₁ tt)))

test-get : Maybe (μ BookstoreF (suc zero))
test-get = runPar (Lens.get (interp BookstoreF bookstore) sbooks)

test-put : Maybe (μ BookstoreF zero)
test-put = runPar (Lens.put (interp BookstoreF bookstore) sbooks vbooks)

test-put' : Maybe (μ BookstoreF zero)
test-put' = runPar (Lens.put (interp BookstoreF bookstore) sbooks vbooks')

test-put'' : Maybe (μ BookstoreF zero)
test-put'' = runPar (Lens.put (interp BookstoreF bookstore) sbooks vbooks'')
