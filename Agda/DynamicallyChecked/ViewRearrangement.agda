open import DynamicallyChecked.Universe
open import Data.Nat

module DynamicallyChecked.ViewRearrangement (n : ℕ) (F : Functor n) where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality

open import Level using (Level)
open import Function
open import Data.Product
open import Data.Bool
open import Data.List 
open import Data.Fin
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


data VarPath : {G : U n} → Pattern F G → U n → Set₁ where
  var    : {G : U n} → VarPath (var {G = G}) G
  child  : {T : U n} {i : Fin n} {pat : Pattern F (F i)} (p : VarPath pat T) → VarPath (child pat) T
  left   : {T G H : U n} {pat : Pattern F G} (p : VarPath pat T) → VarPath (left  {H = H} pat) T
  right  : {T G H : U n} {pat : Pattern F H} (p : VarPath pat T) → VarPath (right {G = G} pat) T
  first  : {T G H : U n} {lpat : Pattern F G} {rpat : Pattern F H} (p : VarPath lpat T) → VarPath (prod lpat rpat) T
  second : {T G H : U n} {lpat : Pattern F G} {rpat : Pattern F H} (p : VarPath rpat T) → VarPath (prod lpat rpat) T
  head   : {T G : U n} {hpat : Pattern F G} {tpat : Pattern F (list G)} (p : VarPath hpat T) → VarPath (elem hpat tpat) T
  tail   : {T G : U n} {hpat : Pattern F G} {tpat : Pattern F (list G)} (p : VarPath tpat T) → VarPath (elem hpat tpat) T

retrieve : {G T : U n} {pat : Pattern F G} → VarPath pat T → PatResult pat → ⟦ T ⟧ (μ F)
retrieve  var       x       = x
retrieve (child  p) x       = retrieve p x
retrieve (left   p) x       = retrieve p x
retrieve (right  p) x       = retrieve p x
retrieve (first  p) (x , y) = retrieve p x
retrieve (second p) (x , y) = retrieve p y
retrieve (head   p) (x , y) = retrieve p x
retrieve (tail   p) (x , y) = retrieve p y

Expr : {G : U n} → Pattern F G → {H : U n} → Pattern F H → Set₁
Expr {G} var          vpat = VarPath vpat G
Expr (k x           ) vpat = ⊤
Expr (child pat     ) vpat = Expr pat vpat
Expr (left pat      ) vpat = Expr pat vpat
Expr (right pat     ) vpat = Expr pat vpat
Expr (prod lpat rpat) vpat = Expr lpat vpat × Expr rpat vpat
Expr (elem hpat tpat) vpat = Expr hpat vpat × Expr tpat vpat

eval : {G : U n} (spat : Pattern F G) {H : U n} (vpat : Pattern F H) → Expr spat vpat → PatResult vpat → PatResult spat
eval var              vpat p              vs = retrieve p vs
eval (k x           ) vpat expr           vs = tt
eval (child spat    ) vpat expr           vs = eval spat vpat expr vs
eval (left spat     ) vpat expr           vs = eval spat vpat expr vs
eval (right spat    ) vpat expr           vs = eval spat vpat expr vs
eval (prod lpat rpat) vpat (expr , expr') vs = eval lpat vpat expr vs , eval rpat vpat expr' vs
eval (elem hpat tpat) vpat (expr , expr') vs = eval hpat vpat expr vs , eval tpat vpat expr' vs

-- nondeterministic expressions
NDExpr : {G : U n} → Pattern F G → {H : U n} → Pattern F H → Set₁
NDExpr vpat spat = ⟦ vpat ⟧ᴾ (List ∘ VarPath spat)

-- devals-var : {G : U n} (spat : Pattern F G) {H : U n} → List (VarPath spat H) → PatResult spat → Par (⟦ H ⟧ (μ F))
-- devals-var spat     []            ss = fail
-- devals-var spat     (p ∷ [])      ss = return (retrieve p ss)
-- devals-var spat {H} (p ∷ p' ∷ ps) ss = devals-var spat (p' ∷ ps) ss >>= λ x →
--                                        case U-dec H (retrieve p ss) x of λ { (yes _) → return x ; (no _) → fail }

-- devals : {G : U n} (spat : Pattern F G) {H : U n} (vpat : Pattern F H) →
--          NDExpr vpat spat → PatResult spat → Par (PatResult vpat)
-- devals spat  var              ps                ss = devals-var spat ps ss
-- devals spat (k x           )  ndexpr            ss = return tt
-- devals spat (child pat     )  ndexpr            ss = devals spat pat ndexpr ss
-- devals spat (left pat      )  ndexpr            ss = devals spat pat ndexpr ss
-- devals spat (right pat     )  ndexpr            ss = devals spat pat ndexpr ss
-- devals spat (prod lpat rpat) (ndexpr , ndexpr') ss = liftPar₂ _,_ (devals spat lpat ndexpr  ss)
--                                                                   (devals spat rpat ndexpr' ss)
-- devals spat (elem hpat tpat) (ndexpr , ndexpr') ss = liftPar₂ _,_ (devals spat hpat ndexpr  ss)
--                                                                   (devals spat tpat ndexpr' ss)

-- deval : {G : U n} (spat : Pattern F G) {H : U n} (vpat : Pattern F H) → NDExpr vpat spat → ⟦ G ⟧ (μ F) → Par (⟦ H ⟧ (μ F))
-- deval spat vpat ndexpr = liftPar (construct vpat) ∘ devals spat vpat ndexpr <=< deconstruct spat

-- update-tip : {l : Level} {G T : U n} {pat : Pattern F G} {f : U n → Set l} → VarPath pat T →
--              (f T → f T) → ⟦ pat ⟧ᴾ f → ⟦ pat ⟧ᴾ f
-- update-tip  var       f x       = f x
-- update-tip (child  p) f x       = update-tip p f x
-- update-tip (left   p) f x       = update-tip p f x
-- update-tip (right  p) f x       = update-tip p f x
-- update-tip (first  p) f (x , y) = update-tip p f x , y
-- update-tip (second p) f (x , y) = x , update-tip p f y
-- update-tip (head   p) f (x , y) = update-tip p f x , y
-- update-tip (tail   p) f (x , y) = x , update-tip p f y

-- empty-ndexpr : {G : U n} (spat : Pattern F G) {H : U n} (vpat : Pattern F H) → NDExpr vpat spat
-- empty-ndexpr spat (var           ) = []
-- empty-ndexpr spat (k x           ) = tt
-- empty-ndexpr spat (child pat     ) = empty-ndexpr spat pat
-- empty-ndexpr spat (left  pat     ) = empty-ndexpr spat pat
-- empty-ndexpr spat (right pat     ) = empty-ndexpr spat pat
-- empty-ndexpr spat (prod lpat rpat) = empty-ndexpr spat lpat , empty-ndexpr spat rpat
-- empty-ndexpr spat (elem hpat tpat) = empty-ndexpr spat hpat , empty-ndexpr spat tpat

-- invert-expr : {G : U n} {spat : Pattern F G} {G' : U n} (spat' : Pattern F G') {H : U n} (vpat : Pattern F H) →
--          ({T : U n} → VarPath spat' T → VarPath spat T) →
--          Expr spat' vpat → NDExpr vpat spat → NDExpr vpat spat
-- invert-expr var              vpat initp p              = update-tip p (_∷_ (initp var))
-- invert-expr (k x           ) vpat initp expr           = id
-- invert-expr (child pat     ) vpat initp expr           = invert-expr pat vpat (initp ∘ child) expr
-- invert-expr (left pat      ) vpat initp expr           = invert-expr pat vpat (initp ∘ left ) expr
-- invert-expr (right pat     ) vpat initp expr           = invert-expr pat vpat (initp ∘ right) expr
-- invert-expr (prod lpat rpat) vpat initp (expr , expr') = invert-expr rpat vpat (initp ∘ second) expr' ∘
--                                                          invert-expr lpat vpat (initp ∘ first ) expr
-- invert-expr (elem hpat tpat) vpat initp (expr , expr') = invert-expr tpat vpat (initp ∘ tail) expr' ∘
--                                                          invert-expr hpat vpat (initp ∘ head) expr

-- toNDExpr : {G : U n} (spat : Pattern F G) {H : U n} (vpat : Pattern F H) → Expr spat vpat → NDExpr vpat spat
-- toNDExpr spat vpat expr = invert-expr spat vpat id expr (empty-ndexpr spat vpat)

-- check-completeness : {G : U n} (spat : Pattern F G) {H : U n} (vpat : Pattern F H) → NDExpr vpat spat → Par ⊤
-- check-completeness spat var              []             = fail
-- check-completeness spat var              (_ ∷ _)        = return tt
-- check-completeness spat (k x           ) expr           = return tt
-- check-completeness spat (child pat     ) expr           = check-completeness spat pat expr
-- check-completeness spat (left pat      ) expr           = check-completeness spat pat expr
-- check-completeness spat (right pat     ) expr           = check-completeness spat pat expr
-- check-completeness spat (prod lpat rpat) (expr , expr') = check-completeness spat lpat expr >>
--                                                           check-completeness spat rpat expr'
-- check-completeness spat (elem hpat tpat) (expr , expr') = check-completeness spat hpat expr >>
--                                                           check-completeness spat tpat expr'

-- from-view : {G : U n} (spat : Pattern F G) {H : U n} (vpat : Pattern F H) →
--             Expr spat vpat → ⟦ H ⟧ (μ F) → Par (⟦ G ⟧ (μ F))
-- from-view spat vpat expr v =
--   check-completeness spat vpat (toNDExpr spat vpat expr) >> eval spat vpat expr v

-- to-view : {G : U n} (spat : Pattern F G) {H : U n} (vpat : Pattern F H) → Expr spat vpat → ⟦ G ⟧ (μ F) → Par (⟦ H ⟧ (μ F))
-- to-view spat vpat expr = deval spat vpat (toNDExpr spat vpat expr)

-- view-rearrangement-iso : {G : U n} (spat : Pattern F G) {H : U n} (vpat : Pattern F H) →
--                          Expr spat vpat → ⟦ G ⟧ (μ F) ≅ ⟦ H ⟧ (μ F)
-- view-rearrangement-iso spat vpat expr = record
--   { to   = to-view   spat vpat expr
--   ; from = from-view spat vpat expr
--   ; to-from-inverse = {!!}
--   ; from-to-inverse = {!!} }
