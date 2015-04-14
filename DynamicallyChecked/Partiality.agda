module DynamicallyChecked.Partiality where

open import Level using (Level)
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Bool
import Data.Maybe as Maybe; open Maybe using (Maybe; just; nothing; maybe)
import Data.Product as Product; open Product
import Data.Sum as Sum; open Sum
open import Data.Nat
open import Data.List
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality


data Par : Set → Set₁ where
  return       : {A   : Set} → A → Par A
  _>>=_        : {A B : Set} → Par A → (A → Par B) → Par B
  fail         : {A   : Set} → Par A
  catch        : {A B : Set} → Par A → (A → Par B) → Par B → Par B
  assert_then_ : {A   : Set} → Bool → Par A → Par A

runPar : {A : Set} → Par A → Maybe A
runPar (return x        ) = just x
runPar (mx >>= f        ) with runPar mx
runPar (mx >>= f        ) | just x  = runPar (f x)
runPar (mx >>= f        ) | nothing = nothing
runPar fail               = nothing
runPar (catch mx f my   ) with runPar mx
runPar (catch mx f my   ) | just x  = runPar (f x)
runPar (catch mx f my   ) | nothing = runPar my
runPar (assert b then mx) = if b then runPar mx else nothing

embed : {A : Set} → Maybe A → Par A
embed = maybe return fail

_>>_ : {A B : Set} → Par A → Par B → Par B
mx >> my = mx >>= const my

infixr 8 _<=<_

_<=<_ : {A B C : Set} → (B → Par C) → (A → Par B) → (A → Par C)
(f <=< g) x = g x >>= f

liftPar : {A B : Set} → (A → B) → Par A → Par B
liftPar f mx = mx >>= λ x → return (f x)

liftPar₂ : {A B C : Set} → (A → B → C) → Par A → Par B → Par C
liftPar₂ f mx my = mx >>= λ x → my >>= λ y → return (f x y)

mapPar : {A B : Set} → (A → Par B) → List A → Par (List B)
mapPar f []       = return []
mapPar f (x ∷ xs) = liftPar₂ _∷_ (f x) (mapPar f xs)

foldrPar : {A B : Set} → (A → B → Par B) → B → List A → Par B
foldrPar f e []       = return e
foldrPar f e (x ∷ xs) = foldrPar f e xs >>= f x

infixr 1 _>>=_
infix 1 assert_then_

mutual

  data CompSeq : {A : Set} → Par A → A → Set₁ where
    return       : {A : Set} {x x' : A} → x ≡ x' → CompSeq (return x) x'
    _>>=_        : {A B : Set} {x : A} {mx : Par A} {f : A → Par B} {y : B} →
                   CompSeq mx x → CompSeq (f x) y → CompSeq (mx >>= f) y
    catch-fst    : {A B : Set} {mx : Par A} {f : A → Par B} {my : Par B} {x : A} {z : B} →
                   CompSeq mx x → CompSeq (f x) z → CompSeq (catch mx f my) z
    catch-snd    : {A B : Set} {mx : Par A} {f : A → Par B} {my : Par B} {z : B} →
                   FailedCompSeq mx → CompSeq my z → CompSeq (catch mx f my) z
    assert_then_ : {A : Set} {b : Bool} {mx : Par A} {x : A} → b ≡ true → CompSeq mx x → CompSeq (assert b then mx) x

  data FailedCompSeq : {A : Set} → Par A → Set₁ where
    bind-fst   : {A B : Set} {mx : Par A} {f : A → Par B} → FailedCompSeq mx → FailedCompSeq (mx >>= f)
    bind-snd   : {A B : Set} {mx : Par A} {x : A} {f : A → Par B} →
                 CompSeq mx x → FailedCompSeq (f x) → FailedCompSeq (mx >>= f)
    fail       : {A : Set} → FailedCompSeq (fail {A})
    catch-fst  : {A B : Set} {mx : Par A} {f : A → Par B} {my : Par B} →
                 FailedCompSeq mx → FailedCompSeq my → FailedCompSeq (catch mx f my)
    catch-snd  : {A B : Set} {mx : Par A} {f : A → Par B} {my : Par B} {x : A} →
                 CompSeq mx x → FailedCompSeq (f x) → FailedCompSeq (catch mx f my)
    assert-fst : {A : Set} {mx : Par A} {b : Bool} → b ≡ false → FailedCompSeq (assert b then mx)
    assert-snd : {A : Set} {mx : Par A} {b : Bool} → b ≡ true → FailedCompSeq mx → FailedCompSeq (assert b then mx)

_↦_ : {A : Set} → Par A → A → Set₁
_↦_ = CompSeq

mutual

  toCompSeq : {A : Set} {mx : Par A} {x : A} → runPar mx ≡ just x → CompSeq mx x
  toCompSeq {mx = return x            } refl = return refl
  toCompSeq {mx = mx >>= f            } eq   with runPar mx | inspect runPar mx
  toCompSeq {mx = mx >>= f            } eq   | just x  | [ runPar-eq ] = toCompSeq runPar-eq >>= toCompSeq eq
  toCompSeq {mx = mx >>= f            } ()   | nothing | _
  toCompSeq {mx = fail                } ()
  toCompSeq {mx = catch mx f my       } eq   with runPar mx | inspect runPar mx
  toCompSeq {mx = catch mx f my       } eq   | just x  | [ runPar-eq ] = catch-fst (toCompSeq runPar-eq) (toCompSeq eq)
  toCompSeq {mx = catch mx f my       } eq   | nothing | [ runPar-eq ] = catch-snd (toFailedCompSeq runPar-eq)
                                                                                   (toCompSeq eq)
  toCompSeq {mx = assert true  then mx} eq   = assert refl then toCompSeq eq
  toCompSeq {mx = assert false then mx} ()

  toFailedCompSeq : {A : Set} {mx : Par A} → runPar mx ≡ nothing → FailedCompSeq mx
  toFailedCompSeq {mx = return x            } ()
  toFailedCompSeq {mx = mx >>= f            } eq with runPar mx | inspect runPar mx
  toFailedCompSeq {mx = mx >>= f            } eq | just x  | [ runPar-eq ] = bind-snd (toCompSeq runPar-eq)
                                                                                      (toFailedCompSeq eq)
  toFailedCompSeq {mx = mx >>= f            } eq | nothing | [ runPar-eq ] = bind-fst (toFailedCompSeq runPar-eq)
  toFailedCompSeq {mx = fail                } eq = fail
  toFailedCompSeq {mx = catch mx f my       } eq with runPar mx | inspect runPar mx
  toFailedCompSeq {mx = catch mx f my       } eq | just x  | [ runPar-eq ] = catch-snd (toCompSeq runPar-eq)
                                                                                       (toFailedCompSeq eq)
  toFailedCompSeq {mx = catch mx f my       } eq | nothing | [ runPar-eq ] = catch-fst (toFailedCompSeq runPar-eq)
                                                                                       (toFailedCompSeq eq)
  toFailedCompSeq {mx = assert true  then mx} eq = assert-snd refl (toFailedCompSeq eq)
  toFailedCompSeq {mx = assert false then mx} eq = assert-fst refl

mutual

  fromCompSeq : {A : Set} {mx : Par A} {x : A} → CompSeq mx x → runPar mx ≡ just x
  fromCompSeq (return refl                   ) = refl
  fromCompSeq (_>>=_ {mx = mx} comp comp'    ) with runPar mx | inspect runPar mx
  fromCompSeq (_>>=_           comp comp'    ) | just x  | [ eq ] with trans (sym eq) (fromCompSeq comp)
  fromCompSeq (_>>=_           comp comp'    ) | just x  | [ eq ] | refl = fromCompSeq comp'
  fromCompSeq (_>>=_           comp comp'    ) | nothing | [ eq ] with trans (sym eq) (fromCompSeq comp)
  fromCompSeq (_>>=_           comp comp'    ) | nothing | [ eq ] | ()
  fromCompSeq (catch-fst {mx = mx} comp comp') with runPar mx | inspect runPar mx
  fromCompSeq (catch-fst           comp comp') | just x  | [ eq ] with trans (sym eq) (fromCompSeq comp)
  fromCompSeq (catch-fst           comp comp') | just x  | [ eq ] | refl = fromCompSeq comp'
  fromCompSeq (catch-fst           comp comp') | nothing | [ eq ] with trans (sym eq) (fromCompSeq comp)
  fromCompSeq (catch-fst           comp comp') | nothing | [ eq ] | ()
  fromCompSeq (catch-snd {mx = mx} fcomp comp) with runPar mx | inspect runPar mx
  fromCompSeq (catch-snd           fcomp comp) | just x  | [ eq ] with trans (sym eq) (fromFailedCompSeq fcomp)
  fromCompSeq (catch-snd           fcomp comp) | just x  | [ eq ] | ()
  fromCompSeq (catch-snd           fcomp comp) | nothing | [ eq ] = fromCompSeq comp
  fromCompSeq (assert refl then comp         ) = fromCompSeq comp

  fromFailedCompSeq : {A : Set} {mx : Par A} → FailedCompSeq mx → runPar mx ≡ nothing
  fromFailedCompSeq (bind-fst {mx = mx} fcomp        ) with runPar mx | inspect runPar mx
  fromFailedCompSeq (bind-fst           fcomp        ) | just x  | [ eq ] with trans (sym eq) (fromFailedCompSeq fcomp)
  fromFailedCompSeq (bind-fst           fcomp        ) | just x  | [ eq ] | ()
  fromFailedCompSeq (bind-fst           fcomp        ) | nothing | [ eq ] = refl
  fromFailedCompSeq (bind-snd {mx = mx} comp fcomp   ) with runPar mx | inspect runPar mx
  fromFailedCompSeq (bind-snd           comp fcomp   ) | just x  | [ eq ] with trans (sym eq) (fromCompSeq comp)
  fromFailedCompSeq (bind-snd           comp fcomp   ) | just x  | [ eq ] | refl = fromFailedCompSeq fcomp
  fromFailedCompSeq (bind-snd           comp fcomp   ) | nothing | [ eq ] with trans (sym eq) (fromCompSeq comp)
  fromFailedCompSeq (bind-snd           comp fcomp   ) | nothing | [ eq ] | ()
  fromFailedCompSeq fail                               = refl
  fromFailedCompSeq (catch-fst {mx = mx} fcomp fcomp') with runPar mx | inspect runPar mx
  fromFailedCompSeq (catch-fst           fcomp fcomp') | just x  | [ eq ] with trans (sym eq) (fromFailedCompSeq fcomp)
  fromFailedCompSeq (catch-fst           fcomp fcomp') | just x  | [ eq ] | ()
  fromFailedCompSeq (catch-fst           fcomp fcomp') | nothing | [ eq ] = fromFailedCompSeq fcomp'
  fromFailedCompSeq (catch-snd {mx = mx} comp fcomp  ) with runPar mx | inspect runPar mx
  fromFailedCompSeq (catch-snd {mx = mx} comp fcomp  ) | just x  | [ eq ] with trans (sym eq) (fromCompSeq comp)
  fromFailedCompSeq (catch-snd {mx = mx} comp fcomp  ) | just x  | [ eq ] | refl = fromFailedCompSeq fcomp
  fromFailedCompSeq (catch-snd {mx = mx} comp fcomp  ) | nothing | [ eq ] with trans (sym eq) (fromCompSeq comp)
  fromFailedCompSeq (catch-snd {mx = mx} comp fcomp  ) | nothing | [ eq ] | ()
  fromFailedCompSeq (assert-fst refl                 ) = refl
  fromFailedCompSeq (assert-snd refl fcomp           ) = fromFailedCompSeq fcomp

succeed-or-fail : {A : Set} (mx : Par A) → (Σ A (CompSeq mx)) ⊎ FailedCompSeq mx
succeed-or-fail mx with runPar mx | inspect runPar mx
succeed-or-fail mx | just x  | [ eq ] = inj₁ (x , toCompSeq eq)
succeed-or-fail mx | nothing | [ eq ] = inj₂ (toFailedCompSeq eq)

either-succeed-or-fail : {A : Set} {mx : Par A} {x : A} → CompSeq mx x → FailedCompSeq mx → ⊥
either-succeed-or-fail {mx = mx} comp fcomp with runPar mx | inspect runPar mx
either-succeed-or-fail {mx = mx} comp fcomp | just x  | [ eq ] with trans (sym eq) (fromFailedCompSeq fcomp)
either-succeed-or-fail {mx = mx} comp fcomp | just x  | [ eq ] | ()
either-succeed-or-fail {mx = mx} comp fcomp | nothing | [ eq ] with trans (sym eq) (fromCompSeq comp)
either-succeed-or-fail {mx = mx} comp fcomp | nothing | [ eq ] | ()

strong-bind-snd : {A B : Set} {mx : Par A} {f : A → Par B} → ((x : A) → FailedCompSeq (f x)) → FailedCompSeq (mx >>= f)
strong-bind-snd {mx = mx} {f} fcomps = toFailedCompSeq aux
  where
    aux : runPar (mx >>= f) ≡ nothing
    aux with runPar mx | inspect runPar mx
    aux | just x  | [ eq ] = fromFailedCompSeq (fcomps x)
    aux | nothing | [ eq ] = refl

record Iso (A B : Set) : Set₁ where
  field
    to   : A → Par B
    from : B → Par A
    to-from-inverse : {x : A} {y : B} → to x ↦ y → from y ↦ x
    from-to-inverse : {y : B} {x : A} → from y ↦ x → to x ↦ y

infix 0 _≅_

_≅_ : Set → Set → Set₁
_≅_ = Iso

id-iso : {A : Set} → A ≅ A
id-iso = record
  { to   = return
  ; from = return
  ; to-from-inverse = λ { {._} (return refl) → return refl }
  ; from-to-inverse = λ { {._} (return refl) → return refl } }

sym-iso : {A B : Set} → A ≅ B → B ≅ A
sym-iso iso = record
  { to   = Iso.from iso
  ; from = Iso.to   iso
  ; to-from-inverse = Iso.from-to-inverse iso
  ; from-to-inverse = Iso.to-from-inverse iso }

trans-iso : {A B C : Set} → A ≅ B → B ≅ C → A ≅ C
trans-iso {A} {B} {C} iso-l iso-r = record
  { to   = Iso.to iso-r <=< Iso.to iso-l
  ; from = Iso.from iso-l <=< Iso.from iso-r
  ; from-to-inverse = λ { (r-comp >>= l-comp) → Iso.from-to-inverse iso-l l-comp >>= Iso.from-to-inverse iso-r r-comp }
  ; to-from-inverse = λ { (l-comp >>= r-comp) → Iso.to-from-inverse iso-r r-comp >>= Iso.to-from-inverse iso-l l-comp } }

prod-unit-iso : {A : Set} → A ≅ A × ⊤
prod-unit-iso = record
  { to   = return ∘ flip _,_ tt
  ; from = return ∘ proj₁
  ; from-to-inverse = λ { {_} {._} (return refl) → return refl }
  ; to-from-inverse = λ { {._}     (return refl) → return refl } }

prod-comm-iso : {A B : Set} → A × B ≅ B × A
prod-comm-iso = record
  { to   = return ∘ swap
  ; from = return ∘ swap
  ; from-to-inverse = λ { {_} {._} (return refl) → return refl }
  ; to-from-inverse = λ { {_} {._} (return refl) → return refl } }

dependency-iso : {A B : Set} → (A → B) → Decidable (_≡_ {A = B}) → A × B ≅ A
dependency-iso {A} {B} f dec =
  record { to = to; from = from; to-from-inverse = to-from-inverse; from-to-inverse = from-to-inverse }
  where
    to : A × B → Par A
    to (a , b) with dec (f a) b
    to (a , b) | yes _ = return a
    to (a , b) | no  _ = fail
    from : A → Par (A × B)
    from = return ∘ < id , f >
    to-from-inverse : {ab : A × B} {a' : A} → to ab ↦ a' → from a' ↦ ab
    to-from-inverse {a , b} comp with dec (f a) b
    to-from-inverse (return refl) | yes refl = return refl
    to-from-inverse ()            | no  _
    from-to-inverse : {a : A} {a'b : A × B} → from a ↦ a'b → to a'b ↦ a
    from-to-inverse {a} (return refl) with dec (f a) (f a)
    from-to-inverse     (return refl) | yes _  = return refl
    from-to-inverse     (return refl) | no neq with neq refl
    from-to-inverse     (return refl) | no neq | ()
