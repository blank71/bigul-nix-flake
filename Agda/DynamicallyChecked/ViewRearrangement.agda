open import DynamicallyChecked.Universe
open import Data.Nat

module DynamicallyChecked.ViewRearrangement (n : ℕ) (F : Functor n) where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality

open import Level using (Level)
open import Function
open import Data.Product
open import Data.Sum
open import Data.Bool
open import Data.Maybe
open import Data.List 
open import Data.Fin
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


VarPath : {G : U n} → Pattern F G → U n → Set₁
VarPath {G} var          T = G ≡ T
VarPath (k x)            T = ⊥
VarPath (child pat)      T = VarPath pat T
VarPath (left  pat)      T = VarPath pat T
VarPath (right pat)      T = VarPath pat T
VarPath (prod lpat rpat) T = VarPath lpat T ⊎ VarPath rpat T
VarPath (elem hpat rpat) T = VarPath hpat T ⊎ VarPath rpat T

retrieve : {G : U n} (pat : Pattern F G) {T : U n} → VarPath pat T → PatResult pat → ⟦ T ⟧ (μ F)
retrieve var              refl        r        = r
retrieve (k x)            ()          r
retrieve (child pat)      path        r        = retrieve pat  path r
retrieve (left  pat)      path        r        = retrieve pat  path r
retrieve (right pat)      path        r        = retrieve pat  path r
retrieve (prod lpat rpat) (inj₁ path) (r , r') = retrieve lpat path r
retrieve (prod lpat rpat) (inj₂ path) (r , r') = retrieve rpat path r'
retrieve (elem hpat tpat) (inj₁ path) (r , r') = retrieve hpat path r
retrieve (elem hpat tpat) (inj₂ path) (r , r') = retrieve tpat path r'

Expr : {G : U n} → Pattern F G → {H : U n} → Pattern F H → Set₁
Expr vpat {H} var          = VarPath vpat H
Expr vpat (k x           ) = ⊤
Expr vpat (child pat     ) = Expr vpat pat
Expr vpat (left pat      ) = Expr vpat pat
Expr vpat (right pat     ) = Expr vpat pat
Expr vpat (prod lpat rpat) = Expr vpat lpat × Expr vpat rpat
Expr vpat (elem hpat tpat) = Expr vpat hpat × Expr vpat tpat

eval : {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) → Expr vpat spat → PatResult vpat → PatResult spat
eval vpat var              p              vs = retrieve vpat p vs
eval vpat (k x           ) expr           vs = tt
eval vpat (child spat    ) expr           vs = eval vpat spat expr vs
eval vpat (left spat     ) expr           vs = eval vpat spat expr vs
eval vpat (right spat    ) expr           vs = eval vpat spat expr vs
eval vpat (prod lpat rpat) (expr , expr') vs = eval vpat lpat expr vs , eval vpat rpat expr' vs
eval vpat (elem hpat tpat) (expr , expr') vs = eval vpat hpat expr vs , eval vpat tpat expr' vs

Container : {G : U n} → Pattern F G → Set
Container pat = ⟦ pat ⟧ᴾ (λ H → Maybe (⟦ H ⟧ (μ F)))

empty-container : {G : U n} (pat : Pattern F G) → Container pat
empty-container pat = defaultᴾ pat _ (λ _ → nothing)

uneval-path : {G : U n} (pat : Pattern F G) {T : U n} → VarPath pat T → ⟦ T ⟧ (μ F) → Container pat → Par (Container pat)
uneval-path {G} var          refl x (just y) with U-dec G x y
uneval-path {G} var          refl x (just y) | yes _ = return (just y)
uneval-path {G} var          refl x (just y) | no  _ = fail
uneval-path var              refl x nothing  = return (just x)
uneval-path (k _)            ()   x c
uneval-path (child pat)      path x c = uneval-path pat path x c
uneval-path (left pat)       path x c = uneval-path pat path x c
uneval-path (right pat)      path x c = uneval-path pat path x c
uneval-path (prod lpat rpat) (inj₁ path) x (c , c') = liftPar (flip _,_ c') (uneval-path lpat path x c )
uneval-path (prod lpat rpat) (inj₂ path) x (c , c') = liftPar (     _,_ c ) (uneval-path rpat path x c')
uneval-path (elem hpat tpat) (inj₁ path) x (c , c') = liftPar (flip _,_ c') (uneval-path hpat path x c )
uneval-path (elem hpat tpat) (inj₂ path) x (c , c') = liftPar (     _,_ c ) (uneval-path tpat path x c')

uneval : {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) →
         Expr vpat spat → PatResult spat → Container vpat → Par (Container vpat)
uneval vpat  var             path             r       = uneval-path vpat path r
uneval vpat (k x           ) expr             r       = return
uneval vpat (child pat     ) expr             r       = uneval vpat pat expr r
uneval vpat (left pat      ) expr             r       = uneval vpat pat expr r
uneval vpat (right pat     ) expr             r       = uneval vpat pat expr r
uneval vpat (prod lpat rpat) (lexpr , rexpr) (r , r') = uneval vpat rpat rexpr r' <=< uneval vpat lpat lexpr r
uneval vpat (elem hpat tpat) (hexpr , texpr) (r , r') = uneval vpat tpat texpr r' <=< uneval vpat hpat hexpr r

fromContainer : {G : U n} (pat : Pattern F G) → Container pat → Par (PatResult pat)
fromContainer  var             (just x) = return x
fromContainer  var             nothing  = fail
fromContainer (k x           ) c        = return tt
fromContainer (child pat     ) c        = fromContainer pat c
fromContainer (left  pat     ) c        = fromContainer pat c
fromContainer (right pat     ) c        = fromContainer pat c
fromContainer (prod lpat rpat) (c , c') = liftPar₂ _,_ (fromContainer lpat c) (fromContainer rpat c')
fromContainer (elem hpat tpat) (c , c') = liftPar₂ _,_ (fromContainer hpat c) (fromContainer tpat c')

CheckTree : {G : U n} → Pattern F G → Set
CheckTree pat = ⟦ pat ⟧ᴾ (const Bool)

runCheckTree-path : {G : U n} (pat : Pattern F G) {T : U n} → VarPath pat T → CheckTree pat → CheckTree pat
runCheckTree-path var              refl        false    = true
runCheckTree-path var              refl        true     = true
runCheckTree-path (k x)            ()          t
runCheckTree-path (child pat)      path        t        = runCheckTree-path pat path t
runCheckTree-path (left  pat)      path        t        = runCheckTree-path pat path t
runCheckTree-path (right pat)      path        t        = runCheckTree-path pat path t
runCheckTree-path (prod lpat rpat) (inj₁ path) (t , t') = runCheckTree-path lpat path t , t'
runCheckTree-path (prod lpat rpat) (inj₂ path) (t , t') = t , runCheckTree-path rpat path t'
runCheckTree-path (elem hpat tpat) (inj₁ path) (t , t') = runCheckTree-path hpat path t , t'
runCheckTree-path (elem hpat tpat) (inj₂ path) (t , t') = t , runCheckTree-path tpat path t'

runCheckTree : {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) →
               Expr vpat spat → CheckTree vpat → CheckTree vpat
runCheckTree vpat var              path            = runCheckTree-path vpat path
runCheckTree vpat (k x           ) expr            = id
runCheckTree vpat (child pat     ) expr            = runCheckTree vpat pat expr
runCheckTree vpat (left pat      ) expr            = runCheckTree vpat pat expr
runCheckTree vpat (right pat     ) expr            = runCheckTree vpat pat expr
runCheckTree vpat (prod lpat rpat) (lexpr , rexpr) = runCheckTree vpat rpat rexpr ∘ runCheckTree vpat lpat lexpr
runCheckTree vpat (elem hpat tpat) (hexpr , texpr) = runCheckTree vpat tpat texpr ∘ runCheckTree vpat hpat hexpr

completeCheckTree : {G : U n} (pat : Pattern F G) → CheckTree pat → Par ⊤
completeCheckTree var               false    = fail
completeCheckTree var               true     = return tt
completeCheckTree (k x            )  t       = return tt
completeCheckTree (child pat      )  t       = completeCheckTree pat t
completeCheckTree (left  pat      )  t       = completeCheckTree pat t
completeCheckTree (right pat      )  t       = completeCheckTree pat t
completeCheckTree (prod  lpat rpat) (t , t') = completeCheckTree lpat t >> completeCheckTree rpat t'
completeCheckTree (elem  hpat tpat) (t , t') = completeCheckTree hpat t >> completeCheckTree tpat t'

empty-checkTree : {G : U n} (pat : Pattern F G) → CheckTree pat
empty-checkTree pat = defaultᴾ pat (const Bool) (const false)

completeExpr : {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) → Expr vpat spat → Par ⊤
completeExpr vpat spat expr = completeCheckTree vpat (runCheckTree vpat spat expr (empty-checkTree vpat))

CompleteExpr : {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) → Expr vpat spat → Set₁
CompleteExpr vpat spat expr = completeExpr vpat spat expr ↦ tt

AbsInterpCCT : {G : U n} (pat : Pattern F G) → Container pat → CheckTree pat → Set
AbsInterpCCT var              (just x) true     = ⊤
AbsInterpCCT var              (just x) false    = ⊥
AbsInterpCCT var              nothing  true     = ⊥
AbsInterpCCT var              nothing  false    = ⊤
AbsInterpCCT (k x)            c        t        = ⊤
AbsInterpCCT (child pat)      c        t        = AbsInterpCCT pat c t
AbsInterpCCT (left  pat)      c        t        = AbsInterpCCT pat c t
AbsInterpCCT (right pat)      c        t        = AbsInterpCCT pat c t
AbsInterpCCT (prod lpat rpat) (c , c') (t , t') = AbsInterpCCT lpat c t × AbsInterpCCT rpat c' t'
AbsInterpCCT (elem hpat tpat) (c , c') (t , t') = AbsInterpCCT hpat c t × AbsInterpCCT tpat c' t'

Consistent : {G : U n} (pat : Pattern F G) → PatResult pat → Container pat → Set
Consistent     var               x        nothing = ⊤
Consistent {G} var               x        (just y) with U-dec G x y
Consistent     var               x        (just y) | yes _ = ⊤
Consistent     var               x        (just y) | no  _ = ⊥
Consistent     (k x)             r        c       = ⊤
Consistent     (child pat)       r        c       = Consistent pat r c
Consistent     (left pat)        r        c       = Consistent pat r c
Consistent     (right pat)       r        c       = Consistent pat r c
Consistent     (prod lpat rpat) (r , r') (c , c') = Consistent lpat r c × Consistent rpat r' c'
Consistent     (elem hpat tpat) (r , r') (c , c') = Consistent hpat r c × Consistent tpat r' c' 

empty-container-consistent :
  {G : U n} (pat : Pattern F G) (r : PatResult pat) → Consistent pat r (empty-container pat)
empty-container-consistent var              r        = tt
empty-container-consistent (k x)            r        = tt
empty-container-consistent (child pat)      r        = empty-container-consistent pat r
empty-container-consistent (left  pat)      r        = empty-container-consistent pat r
empty-container-consistent (right pat)      r        = empty-container-consistent pat r
empty-container-consistent (prod lpat rpat) (r , r') = empty-container-consistent lpat r ,
                                                       empty-container-consistent rpat r'
empty-container-consistent (elem hpat tpat) (r , r') = empty-container-consistent hpat r ,
                                                       empty-container-consistent tpat r'

consistency-eq : {G : U n} {x y : ⟦ G ⟧ (μ F)} → x ≡ y → Consistent {G} var x (just y)
consistency-eq {G} {x} refl with U-dec G x x
consistency-eq {G} {x} refl | yes _   = tt
consistency-eq {G} {x} refl | no  neq with neq refl
consistency-eq {G} {x} refl | no  neq | ()

CompleteContainer : {G : U n} (pat : Pattern F G) → Container pat → Set
CompleteContainer var              nothing  = ⊥
CompleteContainer var              (just _) = ⊤
CompleteContainer (k x)            c        = ⊤
CompleteContainer (child pat)      c        = CompleteContainer pat c
CompleteContainer (left  pat)      c        = CompleteContainer pat c
CompleteContainer (right pat)      c        = CompleteContainer pat c
CompleteContainer (prod lpat rpat) (c , c') = CompleteContainer lpat c × CompleteContainer rpat c'
CompleteContainer (elem hpat tpat) (c , c') = CompleteContainer hpat c × CompleteContainer tpat c'

empty-AbsInterpCCT : {G : U n} (pat : Pattern F G) → AbsInterpCCT pat (empty-container pat) (empty-checkTree pat)
empty-AbsInterpCCT var              = tt
empty-AbsInterpCCT (k x)            = tt
empty-AbsInterpCCT (child pat)      = empty-AbsInterpCCT pat
empty-AbsInterpCCT (left  pat)      = empty-AbsInterpCCT pat
empty-AbsInterpCCT (right pat)      = empty-AbsInterpCCT pat
empty-AbsInterpCCT (prod lpat rpat) = empty-AbsInterpCCT lpat , empty-AbsInterpCCT rpat
empty-AbsInterpCCT (elem hpat tpat) = empty-AbsInterpCCT hpat , empty-AbsInterpCCT tpat

uneval-AbsInterpCCT-path :
  {G : U n} (pat : Pattern F G) {T : U n} (path : VarPath pat T) →
  (x : ⟦ T ⟧ (μ F)) (c : Container pat) (t : CheckTree pat) → AbsInterpCCT pat c t →
  {c' : Container pat} → uneval-path pat path x c ↦ c' → AbsInterpCCT pat c' (runCheckTree-path pat path t)
uneval-AbsInterpCCT-path {G} var          refl x (just y) true  abs comp with U-dec G x y
uneval-AbsInterpCCT-path {G} var          refl x (just y) true  abs (return refl) | yes _ = tt
uneval-AbsInterpCCT-path {G} var          refl x (just y) true  abs ()            | no  _
uneval-AbsInterpCCT-path var              refl x (just y) false ()  comp
uneval-AbsInterpCCT-path var              refl x nothing  true  ()  comp
uneval-AbsInterpCCT-path var              refl x nothing  false abs (return refl) = tt
uneval-AbsInterpCCT-path (k _)            ()   x c t abs comp
uneval-AbsInterpCCT-path (child pat)      path x c t abs comp = uneval-AbsInterpCCT-path pat path x c t abs comp
uneval-AbsInterpCCT-path (left  pat)      path x c t abs comp = uneval-AbsInterpCCT-path pat path x c t abs comp
uneval-AbsInterpCCT-path (right pat)      path x c t abs comp = uneval-AbsInterpCCT-path pat path x c t abs comp
uneval-AbsInterpCCT-path (prod lpat rpat) (inj₁ path) x (c , c') (t , t') (abs , abs') (comp >>= return refl) =
  uneval-AbsInterpCCT-path lpat path x c t abs comp , abs'
uneval-AbsInterpCCT-path (prod lpat rpat) (inj₂ path) x (c , c') (t , t') (abs , abs') (comp >>= return refl) =
  abs , uneval-AbsInterpCCT-path rpat path x c' t' abs' comp
uneval-AbsInterpCCT-path (elem hpat tpat) (inj₁ path) x (c , c') (t , t') (abs , abs') (comp >>= return refl) =
  uneval-AbsInterpCCT-path hpat path x c t abs comp , abs'
uneval-AbsInterpCCT-path (elem hpat tpat) (inj₂ path) x (c , c') (t , t') (abs , abs') (comp >>= return refl) =
  abs , uneval-AbsInterpCCT-path tpat path x c' t' abs' comp

uneval-AbsInterpCCT :
  {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) (expr : Expr vpat spat)
  (r : PatResult spat) (c : Container vpat) (t : CheckTree vpat) → AbsInterpCCT vpat c t →
  {c' : Container vpat} → uneval vpat spat expr r c ↦ c' → AbsInterpCCT vpat c' (runCheckTree vpat spat expr t)
uneval-AbsInterpCCT vpat var              path r c t abs comp = uneval-AbsInterpCCT-path vpat path r c t abs comp
uneval-AbsInterpCCT vpat (k x)            expr r c t abs (return refl) = abs
uneval-AbsInterpCCT vpat (child pat)      expr r c t abs comp = uneval-AbsInterpCCT vpat pat expr r c t abs comp
uneval-AbsInterpCCT vpat (left  pat)      expr r c t abs comp = uneval-AbsInterpCCT vpat pat expr r c t abs comp
uneval-AbsInterpCCT vpat (right pat)      expr r c t abs comp = uneval-AbsInterpCCT vpat pat expr r c t abs comp
uneval-AbsInterpCCT vpat (prod lpat rpat) (lexpr , rexpr) (r , r') c t abs (comp >>= comp') =
  uneval-AbsInterpCCT vpat rpat rexpr r' _ _ (uneval-AbsInterpCCT vpat lpat lexpr r c t abs comp) comp'
uneval-AbsInterpCCT vpat (elem hpat tpat) (hexpr , texpr) (r , r') c t abs (comp >>= comp') =
  uneval-AbsInterpCCT vpat tpat texpr r' _ _ (uneval-AbsInterpCCT vpat hpat hexpr r c t abs comp) comp'

completeCCT : {G : U n} (pat : Pattern F G) (c : Container pat) (t : CheckTree pat) →
              AbsInterpCCT pat c t → completeCheckTree pat t ↦ tt → CompleteContainer pat c
completeCCT var              (just x) t        p        comp = tt
completeCCT var              nothing  true     ()       comp
completeCCT var              nothing  false    p        ()
completeCCT (k x)            c        t        p        comp = tt
completeCCT (child pat)      c        t        p        comp = completeCCT pat c t p comp
completeCCT (left  pat)      c        t        p        comp = completeCCT pat c t p comp
completeCCT (right pat)      c        t        p        comp = completeCCT pat c t p comp
completeCCT (prod lpat rpat) (c , c') (t , t') (p , p') (comp >>= comp') = completeCCT lpat c  t  p  comp ,
                                                                           completeCCT rpat c' t' p' comp'
completeCCT (elem hpat tpat) (c , c') (t , t') (p , p') (comp >>= comp') = completeCCT hpat c  t  p  comp ,
                                                                           completeCCT tpat c' t' p' comp'

fromContainer-consistent-complete :
  {G : U n} (pat : Pattern F G) (r : PatResult pat) (c : Container pat) →
  Consistent pat r c → CompleteContainer pat c → fromContainer pat c ↦ r
fromContainer-consistent-complete {G} var          r (just x) p  q  with U-dec G r x
fromContainer-consistent-complete {G} var          r (just x) p  q  | yes r≡x = return (sym r≡x)
fromContainer-consistent-complete {G} var          r (just x) () q  | no  _
fromContainer-consistent-complete var              r nothing  p  ()
fromContainer-consistent-complete (k x)            r c        p  q  = return refl
fromContainer-consistent-complete (child pat)      r c        p  q  = fromContainer-consistent-complete pat r c p q
fromContainer-consistent-complete (left  pat)      r c        p  q  = fromContainer-consistent-complete pat r c p q
fromContainer-consistent-complete (right pat)      r c        p  q  = fromContainer-consistent-complete pat r c p q
fromContainer-consistent-complete (prod lpat rpat) (r , r') (c , c') (p , p') (q , q') =
  fromContainer-consistent-complete lpat r c p q >>= fromContainer-consistent-complete rpat r' c' p' q' >>= return refl
fromContainer-consistent-complete (elem hpat tpat) (r , r') (c , c') (p , p') (q , q') =
  fromContainer-consistent-complete hpat r c p q >>= fromContainer-consistent-complete tpat r' c' p' q' >>= return refl

eval-uneval-path :
  {G : U n} (vpat : Pattern F G) {H : U n} (path : VarPath vpat H)
  (r : PatResult vpat) (c : Container vpat) → Consistent vpat r c →
  Σ[ c' ∈ Container vpat ] (uneval-path vpat path (retrieve vpat path r) c ↦ c') × Consistent vpat r c'
eval-uneval-path {G} var          refl        r        (just x) p  with U-dec G r x
eval-uneval-path {G} var          refl        r        (just x) p  | yes r≡x = just x , return refl , consistency-eq r≡x
eval-uneval-path {G} var          refl        r        (just x) () | no  r≢x
eval-uneval-path var              refl        r        nothing  p = just r , return refl , consistency-eq refl
eval-uneval-path (k x)            ()          r        c        p
eval-uneval-path (child pat)      path        r        c        p = eval-uneval-path pat path r c p
eval-uneval-path (left  pat)      path        r        c        p = eval-uneval-path pat path r c p
eval-uneval-path (right pat)      path        r        c        p = eval-uneval-path pat path r c p
eval-uneval-path (prod lpat rpat) (inj₁ path) (r , r') (c , c') (p , p') =
  let (c'' , comp , p'') = eval-uneval-path lpat path r c p
  in  (c'' , c') , (comp >>= return refl) , (p'' , p')
eval-uneval-path (prod lpat rpat) (inj₂ path) (r , r') (c , c') (p , p') =
  let (c'' , comp , p'') = eval-uneval-path rpat path r' c' p'
  in  (c , c'') , (comp >>= return refl) , (p , p'')
eval-uneval-path (elem hpat tpat) (inj₁ path) (r , r') (c , c') (p , p') =
  let (c'' , comp , p'') = eval-uneval-path hpat path r c p
  in  (c'' , c') , (comp >>= return refl) , (p'' , p')
eval-uneval-path (elem hpat tpat) (inj₂ path) (r , r') (c , c') (p , p') =
  let (c'' , comp , p'') = eval-uneval-path tpat path r' c' p'
  in  (c , c'') , (comp >>= return refl) , (p , p'')

eval-uneval :
  {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H)
  (expr : Expr vpat spat) (r : PatResult vpat) (c : Container vpat) → Consistent vpat r c →
  Σ[ c' ∈ Container vpat ] (uneval vpat spat expr (eval vpat spat expr r) c ↦ c') × Consistent vpat r c'
eval-uneval vpat var              path r c p = eval-uneval-path vpat path r c p
eval-uneval vpat (k x)            expr r c p = c , return refl , p
eval-uneval vpat (child pat)      expr r c p = eval-uneval vpat pat expr r c p
eval-uneval vpat (left  pat)      expr r c p = eval-uneval vpat pat expr r c p
eval-uneval vpat (right pat)      expr r c p = eval-uneval vpat pat expr r c p
eval-uneval vpat (prod lpat rpat) (lexpr , rexpr) r c p =
  let (c'  , comp'  , p' ) = eval-uneval vpat lpat lexpr r c  p
      (c'' , comp'' , p'') = eval-uneval vpat rpat rexpr r c' p'
  in  c'' , (comp' >>= comp'') , p''
eval-uneval vpat (elem hpat tpat) (hexpr , texpr) r c p =
  let (c'  , comp'  , p' ) = eval-uneval vpat hpat hexpr r c  p
      (c'' , comp'' , p'') = eval-uneval vpat tpat texpr r c' p'
  in  c'' , (comp' >>= comp'') , p''

from-view : {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) →
            Expr vpat spat → ⟦ G ⟧ (μ F) → Par (⟦ H ⟧ (μ F))
from-view vpat spat expr = liftPar (construct spat ∘ eval vpat spat expr) ∘ deconstruct vpat

to-view : {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) → Expr vpat spat → ⟦ H ⟧ (μ F) → Par (⟦ G ⟧ (μ F))
to-view vpat spat expr = liftPar (construct vpat) ∘ fromContainer vpat <=<
                         flip (uneval vpat spat expr) (empty-container vpat) <=< deconstruct spat

to-from-inverse :
  {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H)
  (expr : Expr vpat spat) → CompleteExpr vpat spat expr →
  {xs : ⟦ G ⟧ (μ F)} {ys : ⟦ H ⟧ (μ F)} → from-view vpat spat expr xs ↦ ys → to-view vpat spat expr ys ↦ xs
to-from-inverse vpat spat expr expr-complete (_>>=_ {x = r} deconstruct-vpat-xs↦xs' (return refl)) =
  let (c' , comp' , p') = eval-uneval vpat spat expr r (empty-container vpat) (empty-container-consistent vpat r)
  in  construct-deconstruct-inverse spat _ >>= comp' >>=
      fromContainer-consistent-complete vpat r c' p'
        (completeCCT vpat c' (runCheckTree vpat spat expr (empty-checkTree vpat))
           (uneval-AbsInterpCCT vpat spat expr (eval vpat spat expr r)
              (empty-container vpat) (empty-checkTree vpat) (empty-AbsInterpCCT vpat) comp') expr-complete) >>=
      return (deconstruct-construct-inverse vpat _ deconstruct-vpat-xs↦xs')

view-rearrangement-iso : {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) →
                         (expr : Expr vpat spat) → CompleteExpr vpat spat expr → ⟦ H ⟧ (μ F) ≅ ⟦ G ⟧ (μ F)
view-rearrangement-iso vpat spat expr expr-complete = record
  { to   = to-view   vpat spat expr
  ; from = from-view vpat spat expr
  ; to-from-inverse = {!!}
  ; from-to-inverse = to-from-inverse vpat spat expr expr-complete }
