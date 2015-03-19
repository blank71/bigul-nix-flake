module DynamicallyChecked.Partiality where

open import Level using (Level)
open import Function
open import Data.Unit
open import Data.Bool
import Data.Maybe as Maybe; open Maybe using (Maybe; just; nothing; maybe)
import Data.Product as Product; open Product
import Data.Sum as Sum; open Sum
open import Data.Nat
open import Data.List
open import Relation.Binary.PropositionalEquality


data Par : Set → Set₁ where
  return       : {A   : Set} → A → Par A
  _>>=_        : {A B : Set} → Par A → (A → Par B) → Par B
  fail         : {A   : Set} → Par A
  ⊕            : {A   : Set} → List (Par A) → Par A
  catch        : {A   : Set} → Par A → Par A → Par A
  assert_then_ : {A   : Set} → Bool → Par A → Par A

mutual
  
  runPar : {A : Set} → Par A → Maybe A
  runPar (return x        ) = just x
  runPar (mx >>= f        ) with runPar mx
  runPar (mx >>= f        ) | just x  = runPar (f x)
  runPar (mx >>= f        ) | nothing = nothing
  runPar fail               = nothing
  runPar (⊕ mxs           ) = runPars mxs
  runPar (catch mx my     ) with runPar mx
  runPar (catch mx my     ) | just x  = just x
  runPar (catch mx my     ) | nothing = runPar my
  runPar (assert b then mx) = if b then runPar mx else nothing

  runPars : {A : Set} → List (Par A) → Maybe A
  runPars []         = nothing
  runPars (mx ∷ mxs) with runPar mx
  runPars (mx ∷ mxs) | just x  = runPars' mxs x
  runPars (mx ∷ mxs) | nothing = runPars mxs

  runPars' : {A : Set} → List (Par A) → A → Maybe A
  runPars' []         x = just x
  runPars' (mx ∷ mxs) x with runPar mx 
  runPars' (mx ∷ mxs) x | just _  = nothing
  runPars' (mx ∷ mxs) x | nothing = runPars' mxs x

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

infixr 1 _>>=_
infix 1 assert_then_


data Count {m n : Level} {A : Set m} (P Q : A → Set n) : List A → ℕ → Set n where
  nil  : Count P Q [] 0
  pos : {x : A} {xs : List A} {n : ℕ} → P x → Count P Q xs n → Count P Q (x ∷ xs) (suc n)
  neg : {x : A} {xs : List A} {n : ℕ} → Q x → Count P Q xs n → Count P Q (x ∷ xs) n

mutual

  data CompSeq : {A : Set} → Par A → A → Set₁ where
    return       : {A : Set} {x x' : A} → x ≡ x' → CompSeq (return x) x'
    _>>=_        : {A B : Set} {x : A} {mx : Par A} {f : A → Par B} {y : B} →
                   CompSeq mx x → CompSeq (f x) y → CompSeq (mx >>= f) y
    ⊕            : {A : Set} {mxs : List (Par A)} {y : A} → Count (flip CompSeq y) FailedCompSeq mxs 1 → CompSeq (⊕ mxs) y
    catch-fst    : {A : Set} {mx my : Par A} {z : A} → CompSeq mx z → CompSeq (catch mx my) z
    catch-snd    : {A : Set} {mx my : Par A} {z : A} → FailedCompSeq mx → CompSeq my z → CompSeq (catch mx my) z
    assert_then_ : {A : Set} {b : Bool} {mx : Par A} {x : A} → b ≡ true → CompSeq mx x → CompSeq (assert b then mx) x

  data FailedCompSeq : {A : Set} → Par A → Set₁ where
    bind-fst   : {A B : Set} {mx : Par A} {f : A → Par B} → FailedCompSeq mx → FailedCompSeq (mx >>= f)
    bind-snd   : {A B : Set} {mx : Par A} {x : A} {f : A → Par B} → CompSeq mx x → FailedCompSeq (f x) → FailedCompSeq (mx >>= f)
    fail       : {A : Set} → FailedCompSeq (fail {A})
    ⊕-fst      : {A : Set} {mxs : List (Par A)} → Count (Σ A ∘ CompSeq) FailedCompSeq mxs 0 → FailedCompSeq (⊕ mxs)
    ⊕-snd      : {A : Set} {mxs : List (Par A)} {n : ℕ} → Count (Σ A ∘ CompSeq) FailedCompSeq mxs (2 + n) → FailedCompSeq (⊕ mxs)
    catch      : {A : Set} {mx my : Par A} → FailedCompSeq mx → FailedCompSeq my → FailedCompSeq (catch mx my)
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
  toCompSeq {mx = ⊕ mxs               } eq   = ⊕ (toCompSeq-runPars eq)
  toCompSeq {mx = catch mx my         } eq   with runPar mx | inspect runPar mx
  toCompSeq {mx = catch mx my         } refl | just x  | [ runPar-eq ] = catch-fst (toCompSeq runPar-eq)
  toCompSeq {mx = catch mx my         } eq   | nothing | [ runPar-eq ] = catch-snd (toFailedCompSeq runPar-eq) (toCompSeq eq)
  toCompSeq {mx = assert true  then mx} eq   = assert refl then toCompSeq eq
  toCompSeq {mx = assert false then mx} ()
  
  toCompSeq-runPars : {A : Set} {mxs : List (Par A)} {x : A} → runPars mxs ≡ just x → Count (flip CompSeq x) FailedCompSeq mxs 1
  toCompSeq-runPars {mxs = []      } ()
  toCompSeq-runPars {mxs = mx ∷ mxs} eq with runPar mx | inspect runPar mx
  toCompSeq-runPars {mxs = mx ∷ mxs} eq | just x  | [ runPar-eq ] with toCompSeq-runPars' {mxs = mxs} eq
  toCompSeq-runPars {mxs = mx ∷ mxs} eq | just x  | [ runPar-eq ] | refl , all-failed = pos (toCompSeq runPar-eq) all-failed
  toCompSeq-runPars {mxs = mx ∷ mxs} eq | nothing | [ runPar-eq ] = neg (toFailedCompSeq runPar-eq) (toCompSeq-runPars eq)
  
  toCompSeq-runPars' : {A : Set} {mxs : List (Par A)} {x y : A} → runPars' mxs x ≡ just y → x ≡ y × Count (flip CompSeq x) FailedCompSeq mxs 0
  toCompSeq-runPars' {mxs = []      } refl = refl , nil
  toCompSeq-runPars' {mxs = mx ∷ mxs} eq   with runPar mx | inspect runPar mx
  toCompSeq-runPars' {mxs = mx ∷ mxs} ()   | just x  | [ runPar-eq ]
  toCompSeq-runPars' {mxs = mx ∷ mxs} eq   | nothing | [ runPar-eq ] = Product.map id (neg (toFailedCompSeq runPar-eq)) (toCompSeq-runPars' eq)

  toFailedCompSeq : {A : Set} {mx : Par A} → runPar mx ≡ nothing → FailedCompSeq mx
  toFailedCompSeq {mx = return x            } ()
  toFailedCompSeq {mx = mx >>= f            } eq with runPar mx | inspect runPar mx
  toFailedCompSeq {mx = mx >>= f            } eq | just x  | [ runPar-eq ] = bind-snd (toCompSeq runPar-eq) (toFailedCompSeq eq)
  toFailedCompSeq {mx = mx >>= f            } eq | nothing | [ runPar-eq ] = bind-fst (toFailedCompSeq runPar-eq)
  toFailedCompSeq {mx = fail                } eq = fail
  toFailedCompSeq {mx = ⊕ mxs               } eq with toFailedCompSeq-runPars mxs eq
  toFailedCompSeq {mx = ⊕ mxs               } eq | inj₁ count       = ⊕-fst count
  toFailedCompSeq {mx = ⊕ mxs               } eq | inj₂ (_ , count) = ⊕-snd count
  toFailedCompSeq {mx = catch mx my         } eq with runPar mx | inspect runPar mx
  toFailedCompSeq {mx = catch mx my         } () | just x  | [ runPar-eq ]
  toFailedCompSeq {mx = catch mx my         } eq | nothing | [ runPar-eq ] = catch (toFailedCompSeq runPar-eq) (toFailedCompSeq eq)
  toFailedCompSeq {mx = assert true  then mx} eq = assert-snd refl (toFailedCompSeq eq)
  toFailedCompSeq {mx = assert false then mx} eq = assert-fst refl

  toFailedCompSeq-runPars : {A : Set} (mxs : List (Par A)) → runPars mxs ≡ nothing →
                            Count (Σ A ∘ CompSeq) FailedCompSeq mxs 0 ⊎ Σ[ n ∈ ℕ ] Count (Σ A ∘ CompSeq) FailedCompSeq mxs (2 + n)
  toFailedCompSeq-runPars []         eq = inj₁ nil
  toFailedCompSeq-runPars (mx ∷ mxs) eq with runPar mx | inspect runPar mx
  toFailedCompSeq-runPars (mx ∷ mxs) eq | just x  | [ runPar-eq ] =
    inj₂ (Product.map id (pos (, toCompSeq runPar-eq)) (toFailedCompSeq-runPars' mxs eq))
  toFailedCompSeq-runPars (mx ∷ mxs) eq | nothing | [ runPar-eq ] =
    let fcomp = toFailedCompSeq runPar-eq
    in  Sum.map (neg fcomp) (Product.map id (neg fcomp)) (toFailedCompSeq-runPars mxs eq)
  
  toFailedCompSeq-runPars' : {A : Set} (mxs : List (Par A)) {x : A} → runPars' mxs x ≡ nothing →
                             Σ[ n ∈ ℕ ] Count (Σ A ∘ CompSeq) FailedCompSeq mxs (suc n)
  toFailedCompSeq-runPars' []         ()
  toFailedCompSeq-runPars' (mx ∷ mxs) eq with runPar mx | inspect runPar mx
  toFailedCompSeq-runPars' (mx ∷ mxs) eq | just x  | [ runPar-eq ] =
    Product.map id (pos (, toCompSeq runPar-eq)) (computeCount mxs)
  toFailedCompSeq-runPars' (mx ∷ mxs) eq | nothing | [ runPar-eq ] =
    Product.map id (neg (toFailedCompSeq runPar-eq)) (toFailedCompSeq-runPars' mxs eq)

  computeCount : {A : Set} (mxs : List (Par A)) → Σ[ n ∈ ℕ ] Count (Σ A ∘ CompSeq) FailedCompSeq mxs n
  computeCount []         = 0 , nil
  computeCount (mx ∷ mxs) with runPar mx | inspect runPar mx
  computeCount (mx ∷ mxs) | just x  | [ runPar-eq ] = Product.map suc (pos (, toCompSeq runPar-eq)) (computeCount mxs)
  computeCount (mx ∷ mxs) | nothing | [ runPar-eq ] = Product.map id (neg (toFailedCompSeq runPar-eq)) (computeCount mxs)

-- mutual

--   fromCompSeq : {A : Set} {mx : Par A} {x : A} → CompSeq mx x → runPar mx ≡ just x
--   fromCompSeq (return refl                   ) = refl
--   fromCompSeq (_>>=_ {mx = mx} comp comp'    ) with runPar mx | inspect runPar mx
--   fromCompSeq (_>>=_           comp comp'    ) | just x  | [ eq ] with trans (sym eq) (fromCompSeq comp)
--   fromCompSeq (_>>=_           comp comp'    ) | just x  | [ eq ] | refl = fromCompSeq comp'
--   fromCompSeq (_>>=_           comp comp'    ) | nothing | [ eq ] with trans (sym eq) (fromCompSeq comp)
--   fromCompSeq (_>>=_           comp comp'    ) | nothing | [ eq ] | ()
--   fromCompSeq (_⊕-fst_ {mx = mx} comp fcomp  ) with runPar mx | inspect runPar mx
--   fromCompSeq (_⊕-fst_ {my = my} comp fcomp  ) | just x  | [ runPar-mx-eq ] with runPar my | inspect runPar my
--   fromCompSeq (comp ⊕-fst fcomp              ) | just x  | [ runPar-mx-eq ] | just y  | [ runPar-my-eq ] with trans (sym runPar-my-eq)
--                                                                                                                     (fromFailedCompSeq fcomp)
--   fromCompSeq (comp ⊕-fst fcomp              ) | just x  | [ runPar-mx-eq ] | just y  | [ runPar-my-eq ] | ()
--   fromCompSeq (comp ⊕-fst fcomp              ) | just x  | [ runPar-mx-eq ] | nothing | [ runPar-my-eq ] = trans (sym runPar-mx-eq)
--                                                                                                                  (fromCompSeq comp)
--   fromCompSeq (comp ⊕-fst fcomp              ) | nothing | [ runPar-mx-eq ] with trans (sym runPar-mx-eq) (fromCompSeq comp)
--   fromCompSeq (comp ⊕-fst fcomp              ) | nothing | [ runPar-mx-eq ] | ()
--   fromCompSeq (_⊕-snd_ {mx = mx} fcomp comp  ) with runPar mx | inspect runPar mx
--   fromCompSeq (_⊕-snd_ {my = my} fcomp comp  ) | just x  | [ runPar-mx-eq ] with runPar my
--   fromCompSeq (fcomp ⊕-snd comp              ) | just x  | [ runPar-mx-eq ] | just y  with trans (sym runPar-mx-eq)
--                                                                                                  (fromFailedCompSeq fcomp)
--   fromCompSeq (fcomp ⊕-snd comp              ) | just x  | [ runPar-mx-eq ] | just y  | ()
--   fromCompSeq (fcomp ⊕-snd comp              ) | just x  | [ runPar-mx-eq ] | nothing with trans (sym runPar-mx-eq)
--                                                                                                  (fromFailedCompSeq fcomp)
--   fromCompSeq (fcomp ⊕-snd comp              ) | just x  | [ runPar-mx-eq ] | nothing | ()
--   fromCompSeq (fcomp ⊕-snd comp              ) | nothing | [ runPar-mx-eq ] = fromCompSeq comp
--   fromCompSeq (catch-fst {mx = mx} comp      ) with runPar mx | inspect runPar mx
--   fromCompSeq (catch-fst           comp      ) | just x  | [ eq ] with trans (sym eq) (fromCompSeq comp)
--   fromCompSeq (catch-fst           comp      ) | just x  | [ eq ] | refl = refl
--   fromCompSeq (catch-fst           comp      ) | nothing | [ eq ] with trans (sym eq) (fromCompSeq comp)
--   fromCompSeq (catch-fst           comp      ) | nothing | [ eq ] | ()
--   fromCompSeq (catch-snd {mx = mx} fcomp comp) with runPar mx | inspect runPar mx
--   fromCompSeq (catch-snd {mx = mx} fcomp comp) | just x  | [ eq ] with trans (sym eq) (fromFailedCompSeq fcomp)
--   fromCompSeq (catch-snd {mx = mx} fcomp comp) | just x  | [ eq ] | ()
--   fromCompSeq (catch-snd {mx = mx} fcomp comp) | nothing | [ eq ] = fromCompSeq comp
--   fromCompSeq (assert refl then comp         ) = fromCompSeq comp

--   fromFailedCompSeq : {A : Set} {mx : Par A} → FailedCompSeq mx → runPar mx ≡ nothing
--   fromFailedCompSeq (bind-fst {mx = mx} fcomp      ) with runPar mx | inspect runPar mx
--   fromFailedCompSeq (bind-fst           fcomp      ) | just x  | [ eq ] with trans (sym eq) (fromFailedCompSeq fcomp)
--   fromFailedCompSeq (bind-fst           fcomp      ) | just x  | [ eq ] | ()
--   fromFailedCompSeq (bind-fst           fcomp      ) | nothing | [ eq ] = refl
--   fromFailedCompSeq (bind-snd {mx = mx} comp fcomp ) with runPar mx | inspect runPar mx
--   fromFailedCompSeq (bind-snd           comp fcomp ) | just x  | [ eq ] with trans (sym eq) (fromCompSeq comp)
--   fromFailedCompSeq (bind-snd           comp fcomp ) | just x  | [ eq ] | refl = fromFailedCompSeq fcomp
--   fromFailedCompSeq (bind-snd           comp fcomp ) | nothing | [ eq ] with trans (sym eq) (fromCompSeq comp)
--   fromFailedCompSeq (bind-snd           comp fcomp ) | nothing | [ eq ] | ()
--   fromFailedCompSeq fail                             = refl
--   fromFailedCompSeq (_⊕-fst_ {mx = mx} comp comp'  ) with runPar mx | inspect runPar mx
--   fromFailedCompSeq (_⊕-fst_ {my = my} comp comp'  ) | just x  | [ runPar-mx-eq ] with runPar my | inspect runPar my
--   fromFailedCompSeq (comp ⊕-fst comp'              ) | just x  | [ runPar-mx-eq ] | just y  | [ runPar-my-eq ] = refl
--   fromFailedCompSeq (comp ⊕-fst comp'              ) | just x  | [ runPar-mx-eq ] | nothing | [ runPar-my-eq ] with trans (sym runPar-my-eq)
--                                                                                                                           (fromCompSeq comp')
--   fromFailedCompSeq (comp ⊕-fst comp'              ) | just x  | [ runPar-mx-eq ] | nothing | [ runPar-my-eq ] | ()
--   fromFailedCompSeq (comp ⊕-fst comp'              ) | nothing | [ runPar-mx-eq ] with trans (sym runPar-mx-eq) (fromCompSeq comp)
--   fromFailedCompSeq (comp ⊕-fst comp'              ) | nothing | [ runPar-mx-eq ] | ()
--   fromFailedCompSeq (_⊕-snd_ {mx = mx} fcomp fcomp') with runPar mx | inspect runPar mx
--   fromFailedCompSeq (_⊕-snd_ {my = my} fcomp fcomp') | just x  | [ runPar-mx-eq ] with runPar my
--   fromFailedCompSeq (fcomp ⊕-snd fcomp'            ) | just x  | [ runPar-mx-eq ] | just y  = refl
--   fromFailedCompSeq (fcomp ⊕-snd fcomp'            ) | just x  | [ runPar-mx-eq ] | nothing with trans (sym runPar-mx-eq)
--                                                                                                        (fromFailedCompSeq fcomp)
--   fromFailedCompSeq (fcomp ⊕-snd fcomp'            ) | just x  | [ runPar-mx-eq ] | nothing | ()
--   fromFailedCompSeq (fcomp ⊕-snd fcomp'            ) | nothing | [ runPar-mx-eq ] = fromFailedCompSeq fcomp'
--   fromFailedCompSeq (catch {mx = mx} fcomp fcomp'  ) with runPar mx | inspect runPar mx
--   fromFailedCompSeq (catch           fcomp fcomp'  ) | just x  | [ eq ] with trans (sym eq) (fromFailedCompSeq fcomp)
--   fromFailedCompSeq (catch           fcomp fcomp'  ) | just x  | [ eq ] | ()
--   fromFailedCompSeq (catch           fcomp fcomp'  ) | nothing | [ eq ] = fromFailedCompSeq fcomp'
--   fromFailedCompSeq (assert-fst refl               ) = refl
--   fromFailedCompSeq (assert-snd refl fcomp         ) = fromFailedCompSeq fcomp

-- strong-bind-snd : {A B : Set} {mx : Par A} {f : A → Par B} → ((x : A) → FailedCompSeq (f x)) → FailedCompSeq (mx >>= f)
-- strong-bind-snd {mx = mx} {f} comps = toFailedCompSeq aux
--   where
--     aux : runPar (mx >>= f) ≡ nothing
--     aux with runPar mx | inspect runPar mx
--     aux | just x  | [ eq ] = fromFailedCompSeq (comps x)
--     aux | nothing | [ eq ] = refl

-- record Iso (A B : Set) : Set₁ where
--   field
--     to   : A → Par B
--     from : B → Par A
--     to-from-inverse : {x : A} {y : B} → to x ↦ y → from y ↦ x
--     from-to-inverse : {y : B} {x : A} → from y ↦ x → to x ↦ y

-- infix 0 _≅_

-- _≅_ : Set → Set → Set₁
-- _≅_ = Iso

-- id-iso : {A : Set} → A ≅ A
-- id-iso = record
--   { to   = return
--   ; from = return
--   ; to-from-inverse = λ { {._} (return refl) → return refl }
--   ; from-to-inverse = λ { {._} (return refl) → return refl } }

-- sym-iso : {A B : Set} → A ≅ B → B ≅ A
-- sym-iso iso = record
--   { to   = Iso.from iso
--   ; from = Iso.to   iso
--   ; to-from-inverse = Iso.from-to-inverse iso
--   ; from-to-inverse = Iso.to-from-inverse iso }

-- trans-iso : {A B C : Set} → A ≅ B → B ≅ C → A ≅ C
-- trans-iso {A} {B} {C} iso-l iso-r = record
--   { to   = Iso.to iso-r <=< Iso.to iso-l
--   ; from = Iso.from iso-l <=< Iso.from iso-r
--   ; from-to-inverse = λ { (r-comp >>= l-comp) → Iso.from-to-inverse iso-l l-comp >>= Iso.from-to-inverse iso-r r-comp }
--   ; to-from-inverse = λ { (l-comp >>= r-comp) → Iso.to-from-inverse iso-r r-comp >>= Iso.to-from-inverse iso-l l-comp } }

-- prod-unit-iso : {A : Set} → A ≅ A × ⊤
-- prod-unit-iso = record
--   { to   = return ∘ flip _,_ tt
--   ; from = return ∘ proj₁
--   ; from-to-inverse = λ { {_} {._} (return refl) → return refl }
--   ; to-from-inverse = λ { {._}     (return refl) → return refl } }

-- prod-comm-iso : {A B : Set} → A × B ≅ B × A
-- prod-comm-iso = record
--   { to   = return ∘ swap
--   ; from = return ∘ swap
--   ; from-to-inverse = λ { {_} {._} (return refl) → return refl }
--   ; to-from-inverse = λ { {_} {._} (return refl) → return refl } }
