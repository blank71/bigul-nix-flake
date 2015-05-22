open import DynamicallyChecked.Universe
open import Data.Nat

module DynamicallyChecked.ViewRearrangement {n : ℕ} {F : Functor n} where

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

eval-path : {G : U n} (pat : Pattern F G) {T : U n} → VarPath pat T → PatResult pat → ⟦ T ⟧ (μ F)
eval-path var              refl        r        = r
eval-path (k x)            ()          r
eval-path (child pat)      path        r        = eval-path pat  path r
eval-path (left  pat)      path        r        = eval-path pat  path r
eval-path (right pat)      path        r        = eval-path pat  path r
eval-path (prod lpat rpat) (inj₁ path) (r , r') = eval-path lpat path r
eval-path (prod lpat rpat) (inj₂ path) (r , r') = eval-path rpat path r'
eval-path (elem hpat tpat) (inj₁ path) (r , r') = eval-path hpat path r
eval-path (elem hpat tpat) (inj₂ path) (r , r') = eval-path tpat path r'

Expr : {G : U n} → Pattern F G → {H : U n} → Pattern F H → Set₁
Expr vpat {H} var          = VarPath vpat H
Expr vpat (k x           ) = ⊤
Expr vpat (child pat     ) = Expr vpat pat
Expr vpat (left pat      ) = Expr vpat pat
Expr vpat (right pat     ) = Expr vpat pat
Expr vpat (prod lpat rpat) = Expr vpat lpat × Expr vpat rpat
Expr vpat (elem hpat tpat) = Expr vpat hpat × Expr vpat tpat

eval : {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) → Expr vpat spat → PatResult vpat → PatResult spat
eval vpat var              p              vs = eval-path vpat p vs
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
              AbsInterpCCT pat c t → completeCheckTree pat t ↦ tt → Σ[ r ∈ PatResult pat ] (fromContainer pat c ↦ r)
completeCCT var              (just x) t        p        comp = x , return refl
completeCCT var              nothing  true     ()       comp
completeCCT var              nothing  false    p        ()
completeCCT (k x)            c        t        p        comp = tt , return refl
completeCCT (child pat)      c        t        p        comp = completeCCT pat c t p comp
completeCCT (left  pat)      c        t        p        comp = completeCCT pat c t p comp
completeCCT (right pat)      c        t        p        comp = completeCCT pat c t p comp
completeCCT (prod lpat rpat) (c , c') (t , t') (p , p') (comp >>= comp') =
  let (r  , r-comp ) = completeCCT lpat c  t  p  comp
      (r' , r'-comp) = completeCCT rpat c' t' p' comp'
  in  (r , r') , (r-comp >>= r'-comp >>= return refl)
completeCCT (elem hpat tpat) (c , c') (t , t') (p , p') (comp >>= comp') =
  let (r  , r-comp ) = completeCCT hpat c  t  p  comp
      (r' , r'-comp) = completeCCT tpat c' t' p' comp'
  in  (r , r') , (r-comp >>= r'-comp >>= return refl)

Consistent : {G : U n} (pat : Pattern F G) → PatResult pat → Container pat → Set
Consistent     var               x        nothing  = ⊤
Consistent {G} var               x        (just y) = x ≡ y
Consistent     (k x)             r        c        = ⊤
Consistent     (child pat)       r        c        = Consistent pat r c
Consistent     (left pat)        r        c        = Consistent pat r c
Consistent     (right pat)       r        c        = Consistent pat r c
Consistent     (prod lpat rpat) (r , r') (c , c')  = Consistent lpat r c × Consistent rpat r' c'
Consistent     (elem hpat tpat) (r , r') (c , c')  = Consistent hpat r c × Consistent tpat r' c' 

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

fromContainer-consistent-complete :
  {G : U n} (pat : Pattern F G) (r : PatResult pat) (c : Container pat) →
  Consistent pat r c → {r' : PatResult pat} → fromContainer pat c ↦ r' → r ≡ r'
fromContainer-consistent-complete {G} var     r (just .r) refl (return refl) = refl
fromContainer-consistent-complete var         r nothing   p    ()
fromContainer-consistent-complete (k x)       r c p comp = refl
fromContainer-consistent-complete (child pat) r c p comp = fromContainer-consistent-complete pat r c p comp
fromContainer-consistent-complete (left  pat) r c p comp = fromContainer-consistent-complete pat r c p comp
fromContainer-consistent-complete (right pat) r c p comp = fromContainer-consistent-complete pat r c p comp
fromContainer-consistent-complete (prod lpat rpat) (r , r') (c , c') (p , p') (comp >>= comp' >>= return refl) =
  cong₂ _,_ (fromContainer-consistent-complete lpat r c p comp) (fromContainer-consistent-complete rpat r' c' p' comp')
fromContainer-consistent-complete (elem hpat tpat) (r , r') (c , c') (p , p') (comp >>= comp' >>= return refl) =
  cong₂ _,_ (fromContainer-consistent-complete hpat r c p comp) (fromContainer-consistent-complete tpat r' c' p' comp')

eval-uneval-path :
  {G : U n} (vpat : Pattern F G) {H : U n} (path : VarPath vpat H)
  (r : PatResult vpat) (c : Container vpat) → Consistent vpat r c →
  Σ[ c' ∈ Container vpat ] (uneval-path vpat path (eval-path vpat path r) c ↦ c') × Consistent vpat r c'
eval-uneval-path {G} var          refl        r        (just x) p with U-dec G r x
eval-uneval-path {G} var          refl        r        (just x) p | yes _ = just x , return refl , p
eval-uneval-path {G} var          refl        r        (just x) p | no r≢x with r≢x p
eval-uneval-path {G} var          refl        r        (just x) p | no r≢x | ()
eval-uneval-path var              refl        r        nothing  p = just r , return refl , refl
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
  {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) (expr : Expr vpat spat)
  (r : PatResult vpat) (c : Container vpat) → Consistent vpat r c →
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

FullEmbedding-path :
  {G : U n} (pat : Pattern F G) {T : U n} (path : VarPath pat T) →
  ⟦ T ⟧ (μ F) → Container pat → Set
FullEmbedding-path var              refl x c = c ≡ just x
FullEmbedding-path (k _)            ()   x c
FullEmbedding-path (child pat)      path x c = FullEmbedding-path pat path x c
FullEmbedding-path (left  pat)      path x c = FullEmbedding-path pat path x c
FullEmbedding-path (right pat)      path x c = FullEmbedding-path pat path x c
FullEmbedding-path (prod lpat rpat) (inj₁ path) x (c , c') = FullEmbedding-path lpat path x c
FullEmbedding-path (prod lpat rpat) (inj₂ path) x (c , c') = FullEmbedding-path rpat path x c'
FullEmbedding-path (elem hpat tpat) (inj₁ path) x (c , c') = FullEmbedding-path hpat path x c
FullEmbedding-path (elem hpat tpat) (inj₂ path) x (c , c') = FullEmbedding-path tpat path x c'

FullEmbedding :
  {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) (expr : Expr vpat spat) →
  PatResult spat → Container vpat → Set
FullEmbedding vpat var              path            r        c = FullEmbedding-path vpat path r c
FullEmbedding vpat (k x)            expr            r        c = ⊤
FullEmbedding vpat (child pat)      expr            r        c = FullEmbedding vpat pat expr r c
FullEmbedding vpat (left  pat)      expr            r        c = FullEmbedding vpat pat expr r c
FullEmbedding vpat (right pat)      expr            r        c = FullEmbedding vpat pat expr r c
FullEmbedding vpat (prod lpat rpat) (lexpr , rexpr) (r , r') c = FullEmbedding vpat lpat lexpr r  c ×
                                                                 FullEmbedding vpat rpat rexpr r' c
FullEmbedding vpat (elem hpat tpat) (hexpr , texpr) (r , r') c = FullEmbedding vpat hpat hexpr r  c ×
                                                                 FullEmbedding vpat tpat texpr r' c

Extension : {G : U n} (pat : Pattern F G) → Container pat → Container pat → Set
Extension var              nothing  d        = ⊤
Extension var              (just x) d        = d ≡ just x
Extension (k x)            c        d        = ⊤
Extension (child pat)      c        d        = Extension pat c d 
Extension (left  pat)      c        d        = Extension pat c d 
Extension (right pat)      c        d        = Extension pat c d 
Extension (prod lpat rpat) (c , c') (d , d') = Extension lpat c d × Extension rpat c' d'
Extension (elem hpat tpat) (c , c') (d , d') = Extension hpat c d × Extension tpat c' d'

Extension-reflexive : 
  {G : U n} (pat : Pattern F G) (c : Container pat) → Extension pat c c
Extension-reflexive var         nothing  = tt 
Extension-reflexive var         (just _) = refl 
Extension-reflexive (k x)       c = tt 
Extension-reflexive (child pat) c = Extension-reflexive pat c 
Extension-reflexive (left  pat) c = Extension-reflexive pat c 
Extension-reflexive (right pat) c = Extension-reflexive pat c 
Extension-reflexive (prod lpat rpat) (c , c') = Extension-reflexive lpat c , Extension-reflexive rpat c'
Extension-reflexive (elem hpat tpat) (c , c') = Extension-reflexive hpat c , Extension-reflexive tpat c'

Extension-transitive : 
  {G : U n} (pat : Pattern F G) (c d e : Container pat) → Extension pat c d → Extension pat d e → Extension pat c e
Extension-transitive var         nothing  d  e  excd exde = tt
Extension-transitive var         (just x) ._ ._ refl refl = refl
Extension-transitive (k x)       c d e excd exde = tt
Extension-transitive (child pat) c d e excd exde = Extension-transitive pat c d e excd exde
Extension-transitive (left  pat) c d e excd exde = Extension-transitive pat c d e excd exde
Extension-transitive (right pat) c d e excd exde = Extension-transitive pat c d e excd exde
Extension-transitive (prod lpat rpat) (c , c') (d , d') (e , e') (excd , excd') (exde , exde') =
  Extension-transitive lpat c d e excd exde , Extension-transitive rpat c' d' e' excd' exde'
Extension-transitive (elem hpat tpat) (c , c') (d , d') (e , e') (excd , excd') (exde , exde') =
  Extension-transitive hpat c d e excd exde , Extension-transitive tpat c' d' e' excd' exde'

FullEmbedding-path-Extension :
  {G : U n} (pat : Pattern F G) {T : U n} (path : VarPath pat T) →
  (x : ⟦ T ⟧ (μ F)) (c d : Container pat) →
  FullEmbedding-path pat path x c → Extension pat c d → FullEmbedding-path pat path x d
FullEmbedding-path-Extension var              refl x ._ ._ refl refl = refl
FullEmbedding-path-Extension (k _)            ()   x c d fe ex
FullEmbedding-path-Extension (child pat)      path x c d fe ex = FullEmbedding-path-Extension pat path x c d fe ex
FullEmbedding-path-Extension (left  pat)      path x c d fe ex = FullEmbedding-path-Extension pat path x c d fe ex
FullEmbedding-path-Extension (right pat)      path x c d fe ex = FullEmbedding-path-Extension pat path x c d fe ex
FullEmbedding-path-Extension (prod lpat rpat) (inj₁ path) x (c , c') (d , d') fe (ex , ex') =
  FullEmbedding-path-Extension lpat path x c d fe ex
FullEmbedding-path-Extension (prod lpat rpat) (inj₂ path) x (c , c') (d , d') fe (ex , ex') =
  FullEmbedding-path-Extension rpat path x c' d' fe ex'
FullEmbedding-path-Extension (elem hpat tpat) (inj₁ path) x (c , c') (d , d') fe (ex , ex') =
  FullEmbedding-path-Extension hpat path x c d fe ex
FullEmbedding-path-Extension (elem hpat tpat) (inj₂ path) x (c , c') (d , d') fe (ex , ex') =
  FullEmbedding-path-Extension tpat path x c' d' fe ex'

FullEmbedding-Extension :
  {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) (expr : Expr vpat spat) →
  (r : PatResult spat) (c c' : Container vpat) →
  FullEmbedding vpat spat expr r c → Extension vpat c c' → FullEmbedding vpat spat expr r c'
FullEmbedding-Extension vpat var              path r c c' fe ex = FullEmbedding-path-Extension vpat path r c c' fe ex
FullEmbedding-Extension vpat (k x)            expr r c c' fe ex = tt
FullEmbedding-Extension vpat (child pat)      expr r c c' fe ex = FullEmbedding-Extension vpat pat expr r c c' fe ex
FullEmbedding-Extension vpat (left  pat)      expr r c c' fe ex = FullEmbedding-Extension vpat pat expr r c c' fe ex
FullEmbedding-Extension vpat (right pat)      expr r c c' fe ex = FullEmbedding-Extension vpat pat expr r c c' fe ex
FullEmbedding-Extension vpat (prod lpat rpat) (lexpr , rexpr) (r , r') c c' (fe , fe') ex =
  FullEmbedding-Extension vpat lpat lexpr r c c' fe ex , FullEmbedding-Extension vpat rpat rexpr r' c c' fe' ex
FullEmbedding-Extension vpat (elem hpat tpat) (hexpr , texpr) (r , r') c c' (fe , fe') ex =
  FullEmbedding-Extension vpat hpat hexpr r c c' fe ex , FullEmbedding-Extension vpat tpat texpr r' c c' fe' ex

uneval-path-Extension :
  {G : U n} (pat : Pattern F G) {T : U n} (path : VarPath pat T) →
  (x : ⟦ T ⟧ (μ F)) (c : Container pat) {c' : Container pat} →
  uneval-path pat path x c ↦ c' → Extension pat c c'
uneval-path-Extension var              refl x nothing  uneval-path↦ = tt
uneval-path-Extension {G} var          refl x (just y) uneval-path↦ with U-dec G x y
uneval-path-Extension {G} var          refl x (just y) (return refl) | yes _ = refl
uneval-path-Extension {G} var          refl x (just y) ()            | no  _
uneval-path-Extension (k _)            ()   x c uneval-path↦
uneval-path-Extension (child pat)      path x c uneval-path↦ = uneval-path-Extension pat path x c uneval-path↦
uneval-path-Extension (left  pat)      path x c uneval-path↦ = uneval-path-Extension pat path x c uneval-path↦
uneval-path-Extension (right pat)      path x c uneval-path↦ = uneval-path-Extension pat path x c uneval-path↦
uneval-path-Extension (prod lpat rpat) (inj₁ path) x (c , c') (uneval-path↦ >>= return refl) =
  uneval-path-Extension lpat path x c uneval-path↦ , Extension-reflexive rpat c'
uneval-path-Extension (prod lpat rpat) (inj₂ path) x (c , c') (uneval-path↦ >>= return refl) =
  Extension-reflexive lpat c , uneval-path-Extension rpat path x c' uneval-path↦
uneval-path-Extension (elem hpat tpat) (inj₁ path) x (c , c') (uneval-path↦ >>= return refl) =
  uneval-path-Extension hpat path x c uneval-path↦ , Extension-reflexive tpat c'
uneval-path-Extension (elem hpat tpat) (inj₂ path) x (c , c') (uneval-path↦ >>= return refl) =
  Extension-reflexive hpat c , uneval-path-Extension tpat path x c' uneval-path↦

uneval-Extension :
  {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) (expr : Expr vpat spat) →
  (r : PatResult spat) (c : Container vpat) {c' : Container vpat} →
  uneval vpat spat expr r c ↦ c' → Extension vpat c c'
uneval-Extension vpat var              path r c uneval↦ = uneval-path-Extension vpat path r c uneval↦
uneval-Extension vpat (k x)            expr r c (return refl) = Extension-reflexive vpat c
uneval-Extension vpat (child pat)      expr r c uneval↦ = uneval-Extension vpat pat expr r c uneval↦
uneval-Extension vpat (left  pat)      expr r c uneval↦ = uneval-Extension vpat pat expr r c uneval↦
uneval-Extension vpat (right pat)      expr r c uneval↦ = uneval-Extension vpat pat expr r c uneval↦
uneval-Extension vpat (prod lpat rpat) (lexpr , rexpr) (r , r') c (uneval↦ >>= uneval↦') =
  Extension-transitive vpat _ _ _ (uneval-Extension vpat lpat lexpr r  c uneval↦ )
                                  (uneval-Extension vpat rpat rexpr r' _ uneval↦')
uneval-Extension vpat (elem hpat tpat) (hexpr , texpr) (r , r') c (uneval↦ >>= uneval↦') =
  Extension-transitive vpat _ _ _ (uneval-Extension vpat hpat hexpr r  c uneval↦ )
                                  (uneval-Extension vpat tpat texpr r' _ uneval↦')

uneval-path-FullEmbedding :
  {G : U n} (pat : Pattern F G) {T : U n} (path : VarPath pat T) →
  (x : ⟦ T ⟧ (μ F)) (c : Container pat) {c' : Container pat} →
  uneval-path pat path x c ↦ c' → FullEmbedding-path pat path x c'
uneval-path-FullEmbedding var         refl x nothing  (return refl) = refl
uneval-path-FullEmbedding {G} var     refl x (just y) uneval-path↦ with U-dec G x y
uneval-path-FullEmbedding var         refl x (just y) (return refl) | yes x≡y = cong just (sym x≡y)
uneval-path-FullEmbedding var         refl x (just y) ()            | no  _
uneval-path-FullEmbedding (k _)       ()   x c uneval-path↦
uneval-path-FullEmbedding (child pat) path x c uneval-path↦ = uneval-path-FullEmbedding pat path x c uneval-path↦
uneval-path-FullEmbedding (left  pat) path x c uneval-path↦ = uneval-path-FullEmbedding pat path x c uneval-path↦
uneval-path-FullEmbedding (right pat) path x c uneval-path↦ = uneval-path-FullEmbedding pat path x c uneval-path↦
uneval-path-FullEmbedding (prod lpat rpat) (inj₁ path) x (c , c') (uneval-path↦ >>= return refl) =
  uneval-path-FullEmbedding lpat path x c uneval-path↦
uneval-path-FullEmbedding (prod lpat rpat) (inj₂ path) x (c , c') (uneval-path↦ >>= return refl) =
  uneval-path-FullEmbedding rpat path x c' uneval-path↦
uneval-path-FullEmbedding (elem hpat tpat) (inj₁ path) x (c , c') (uneval-path↦ >>= return refl) =
  uneval-path-FullEmbedding hpat path x c uneval-path↦
uneval-path-FullEmbedding (elem hpat tpat) (inj₂ path) x (c , c') (uneval-path↦ >>= return refl) =
  uneval-path-FullEmbedding tpat path x c' uneval-path↦

uneval-FullEmbedding :
  {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) (expr : Expr vpat spat) →
  (r : PatResult spat) (c : Container vpat) {c' : Container vpat} →
  uneval vpat spat expr r c ↦ c' → FullEmbedding vpat spat expr r c'
uneval-FullEmbedding vpat var              path r c uneval↦ = uneval-path-FullEmbedding vpat path r c uneval↦
uneval-FullEmbedding vpat (k x)            expr r c uneval↦ = tt
uneval-FullEmbedding vpat (child pat)      expr r c uneval↦ = uneval-FullEmbedding vpat pat expr r c uneval↦
uneval-FullEmbedding vpat (left  pat)      expr r c uneval↦ = uneval-FullEmbedding vpat pat expr r c uneval↦
uneval-FullEmbedding vpat (right pat)      expr r c uneval↦ = uneval-FullEmbedding vpat pat expr r c uneval↦
uneval-FullEmbedding vpat (prod lpat rpat) (lexpr , rexpr) (r , r') c (uneval↦ >>= uneval↦') =
  FullEmbedding-Extension vpat lpat lexpr r _ _ (uneval-FullEmbedding vpat lpat lexpr r  _ uneval↦ )
                                                (uneval-Extension     vpat rpat rexpr r' _ uneval↦') ,
  uneval-FullEmbedding vpat rpat rexpr r' _ uneval↦'
uneval-FullEmbedding vpat (elem hpat tpat) (hexpr , texpr) (r , r') c (uneval↦ >>= uneval↦') =
  FullEmbedding-Extension vpat hpat hexpr r _ _ (uneval-FullEmbedding vpat hpat hexpr r  _ uneval↦ )
                                                (uneval-Extension     vpat tpat texpr r' _ uneval↦') ,
  uneval-FullEmbedding vpat tpat texpr r' _ uneval↦'

uneval-eval-path :
  {G : U n} (pat : Pattern F G) {T : U n} (path : VarPath pat T)
  (x : ⟦ T ⟧ (μ F)) (c : Container pat) {r : PatResult pat} →
  FullEmbedding-path pat path x c → fromContainer pat c ↦ r → eval-path pat path r ≡ x
uneval-eval-path var         refl x ._ refl (return refl)  = refl
uneval-eval-path (k _)       ()   x c  fe   fromContainer↦
uneval-eval-path (child pat) path x c  fe   fromContainer↦ = uneval-eval-path pat path x c fe fromContainer↦
uneval-eval-path (left  pat) path x c  fe   fromContainer↦ = uneval-eval-path pat path x c fe fromContainer↦
uneval-eval-path (right pat) path x c  fe   fromContainer↦ = uneval-eval-path pat path x c fe fromContainer↦
uneval-eval-path (prod lpat rpat) (inj₁ path) x (c , c') fe (fromContainer↦ >>= _ >>= return refl) =
  uneval-eval-path lpat path x c fe fromContainer↦
uneval-eval-path (prod lpat rpat) (inj₂ path) x (c , c') fe (_ >>= fromContainer↦ >>= return refl) =
  uneval-eval-path rpat path x c' fe fromContainer↦
uneval-eval-path (elem hpat tpat) (inj₁ path) x (c , c') fe (fromContainer↦ >>= _ >>= return refl) =
  uneval-eval-path hpat path x c fe fromContainer↦
uneval-eval-path (elem hpat tpat) (inj₂ path) x (c , c') fe (_ >>= fromContainer↦ >>= return refl) =
  uneval-eval-path tpat path x c' fe fromContainer↦

uneval-eval :
  {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) (expr : Expr vpat spat)
  (r : PatResult spat) {r' : PatResult vpat} (c : Container vpat) →
  FullEmbedding vpat spat expr r c → fromContainer vpat c ↦ r' → eval vpat spat expr r' ≡ r
uneval-eval vpat var              path r c fe fromContainer↦ = uneval-eval-path vpat path r c fe fromContainer↦
uneval-eval vpat (k x)            expr r c fe fromContainer↦ = refl
uneval-eval vpat (child pat)      expr r c fe fromContainer↦ = uneval-eval vpat pat expr r c fe fromContainer↦
uneval-eval vpat (left  pat)      expr r c fe fromContainer↦ = uneval-eval vpat pat expr r c fe fromContainer↦
uneval-eval vpat (right pat)      expr r c fe fromContainer↦ = uneval-eval vpat pat expr r c fe fromContainer↦
uneval-eval vpat (prod lpat rpat) (lexpr , rexpr) (r , r') c (fe , fe') fromContainer↦ =
  cong₂ _,_ (uneval-eval vpat lpat lexpr r c fe fromContainer↦) (uneval-eval vpat rpat rexpr r' c fe' fromContainer↦)
uneval-eval vpat (elem hpat tpat) (hexpr , texpr) (r , r') c (fe , fe') fromContainer↦ =
  cong₂ _,_ (uneval-eval vpat hpat hexpr r c fe fromContainer↦) (uneval-eval vpat tpat texpr r' c fe' fromContainer↦)

from-view : {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) →
            Expr vpat spat → ⟦ G ⟧ (μ F) → Par (⟦ H ⟧ (μ F))
from-view vpat spat expr = liftPar (construct spat ∘ eval vpat spat expr) ∘ deconstruct vpat

to-view : {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) → Expr vpat spat → ⟦ H ⟧ (μ F) → Par (⟦ G ⟧ (μ F))
to-view vpat spat expr = liftPar (construct vpat) ∘ fromContainer vpat <=<
                         flip (uneval vpat spat expr) (empty-container vpat) <=< deconstruct spat

to-from-inverse :
  {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H)
  (expr : Expr vpat spat) → CompleteExpr vpat spat expr →
  {x : ⟦ G ⟧ (μ F)} {y : ⟦ H ⟧ (μ F)} → from-view vpat spat expr x ↦ y → to-view vpat spat expr y ↦ x
to-from-inverse vpat spat expr expr-complete (_>>=_ {x = r} deconstruct-vpat-x↦x' (return refl)) =
  let (c' , comp' , p') = eval-uneval vpat spat expr r (empty-container vpat) (empty-container-consistent vpat r)
      (r' , r'-comp) = completeCCT vpat c' (runCheckTree vpat spat expr (empty-checkTree vpat))
                         (uneval-AbsInterpCCT vpat spat expr (eval vpat spat expr r)
                            (empty-container vpat) (empty-checkTree vpat) (empty-AbsInterpCCT vpat) comp') expr-complete
  in  construct-deconstruct-inverse spat _ >>= comp' >>= r'-comp >>=
      return (trans (cong (construct vpat) (sym (fromContainer-consistent-complete vpat r c' p' r'-comp)))
                    (deconstruct-construct-inverse vpat _ deconstruct-vpat-x↦x'))

from-to-inverse :
  {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H)
  (expr : Expr vpat spat) → CompleteExpr vpat spat expr →
  {x : ⟦ G ⟧ (μ F)} {y : ⟦ H ⟧ (μ F)} → to-view vpat spat expr y ↦ x → from-view vpat spat expr x ↦ y
from-to-inverse vpat spat expr expr-complete (deconstruct-spat↦ >>= uneval↦ >>= fromContainer↦ >>= return refl) =
  construct-deconstruct-inverse vpat _ >>=
  return (trans (cong (construct spat)
                      (uneval-eval vpat spat expr _ _ (uneval-FullEmbedding vpat spat expr _ _ uneval↦) fromContainer↦))
                (deconstruct-construct-inverse spat _ deconstruct-spat↦))

view-rearrangement-iso : {G : U n} (vpat : Pattern F G) {H : U n} (spat : Pattern F H) →
                         (expr : Expr vpat spat) → CompleteExpr vpat spat expr → ⟦ H ⟧ (μ F) ≅ ⟦ G ⟧ (μ F)
view-rearrangement-iso vpat spat expr expr-complete = record
  { to   = to-view   vpat spat expr
  ; from = from-view vpat spat expr
  ; to-from-inverse = from-to-inverse vpat spat expr expr-complete
  ; from-to-inverse = to-from-inverse vpat spat expr expr-complete }
