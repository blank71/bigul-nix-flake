open import DynamicallyChecked.Universe
open import Data.Nat

module DynamicallyChecked.Rearrangement {n : ℕ} {F : Functor n} where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens

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
VarPath (left  pat)      T = VarPath pat T
VarPath (right pat)      T = VarPath pat T
VarPath (prod lpat rpat) T = VarPath lpat T ⊎ VarPath rpat T
VarPath (con pat)        T = VarPath pat T

eval-path : {G : U n} (pat : Pattern F G) {T : U n} → VarPath pat T → PatResult pat → ⟦ T ⟧ (μ F)
eval-path var              refl        r        = r
eval-path (k x)            ()          r
eval-path (left  pat)      path        r        = eval-path pat  path r
eval-path (right pat)      path        r        = eval-path pat  path r
eval-path (prod lpat rpat) (inj₁ path) (r , r') = eval-path lpat path r
eval-path (prod lpat rpat) (inj₂ path) (r , r') = eval-path rpat path r'
eval-path (con pat)        path        r        = eval-path pat  path r

Expr : {G : U n} → Pattern F G → {H : U n} → Pattern F H → Set₁
Expr p {H} var          = VarPath p H
Expr p (k x)            = ⊤
Expr p (left  pat)      = Expr p pat
Expr p (right pat)      = Expr p pat
Expr p (prod lpat rpat) = Expr p lpat × Expr p rpat
Expr p (con pat)        = Expr p pat

eval : {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) → Expr pat pat' → PatResult pat → PatResult pat'
eval pat var              p              vs = eval-path pat p vs
eval pat (k x           ) expr           vs = tt
eval pat (left  pat'    ) expr           vs = eval pat pat' expr vs
eval pat (right pat'    ) expr           vs = eval pat pat' expr vs
eval pat (prod lpat rpat) (expr , expr') vs = eval pat lpat expr vs , eval pat rpat expr' vs
eval pat (con pat'      ) expr           vs = eval pat pat' expr vs

Container : {G : U n} → Pattern F G → Set
Container pat = ⟦ pat ⟧ᴾ (λ H → Maybe (⟦ H ⟧ (μ F)))

empty-container : {G : U n} (pat : Pattern F G) → Container pat
empty-container pat = defaultᴾ pat _ (λ _ → nothing)

uneval-path : {G : U n} (pat : Pattern F G) {T : U n} → VarPath pat T → ⟦ T ⟧ (μ F) → Container pat → Par (Container pat)
uneval-path {G} var              refl        x (just y) with U-dec G x y
uneval-path {G} var              refl        x (just y) | yes _ = return (just y)
uneval-path {G} var              refl        x (just y) | no  _ = fail
uneval-path     var              refl        x nothing  = return (just x)
uneval-path     (k _)            ()          x c
uneval-path     (left  pat)      path        x c        = uneval-path pat path x c
uneval-path     (right pat)      path        x c        = uneval-path pat path x c
uneval-path     (prod lpat rpat) (inj₁ path) x (c , c') = liftPar (flip _,_ c') (uneval-path lpat path x c )
uneval-path     (prod lpat rpat) (inj₂ path) x (c , c') = liftPar (     _,_ c ) (uneval-path rpat path x c')
uneval-path     (con pat)        path        x c        = uneval-path pat path x c

uneval : {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) →
         Expr pat pat' → PatResult pat' → Container pat → Par (Container pat)
uneval p  var             path             r       = uneval-path p path r
uneval p (k x)            expr             r       = return
uneval p (left  pat)      expr             r       = uneval p pat expr r
uneval p (right pat)      expr             r       = uneval p pat expr r
uneval p (prod lpat rpat) (lexpr , rexpr) (r , r') = uneval p rpat rexpr r' <=< uneval p lpat lexpr r
uneval p (con pat)        expr             r       = uneval p pat expr r

Consistent : {G : U n} (pat : Pattern F G) → PatResult pat → Container pat → Set
Consistent     var              x        nothing  = ⊤
Consistent {G} var              x        (just y) = x ≡ y
Consistent     (k x)            r        c        = ⊤
Consistent     (left  pat)      r        c        = Consistent pat r c
Consistent     (right pat)      r        c        = Consistent pat r c
Consistent     (prod lpat rpat) (r , r') (c , c') = Consistent lpat r c × Consistent rpat r' c'
Consistent     (con pat)        r        c        = Consistent pat r c

empty-container-consistent :
  {G : U n} (pat : Pattern F G) (r : PatResult pat) → Consistent pat r (empty-container pat)
empty-container-consistent var              r        = tt
empty-container-consistent (k x)            r        = tt
empty-container-consistent (left  pat)      r        = empty-container-consistent pat r
empty-container-consistent (right pat)      r        = empty-container-consistent pat r
empty-container-consistent (prod lpat rpat) (r , r') = empty-container-consistent lpat r ,
                                                       empty-container-consistent rpat r'
empty-container-consistent (con pat)        r        = empty-container-consistent pat r

eval-uneval-path :
  {G : U n} (pat : Pattern F G) {H : U n} (path : VarPath pat H)
  (r : PatResult pat) (c : Container pat) → Consistent pat r c →
  Σ[ c' ∈ Container pat ] ((uneval-path pat path (eval-path pat path r) c ↦ c') × Consistent pat r c')
eval-uneval-path {G} var              refl        r        (just x) p with U-dec G r x
eval-uneval-path {G} var              refl        r        (just x) p | yes _ = just x , return refl , p
eval-uneval-path {G} var              refl        r        (just x) p | no r≢x with r≢x p
eval-uneval-path {G} var              refl        r        (just x) p | no r≢x | ()
eval-uneval-path     var              refl        r        nothing  p = just r , return refl , refl
eval-uneval-path     (k x)            ()          r        c        p
eval-uneval-path     (left  pat)      path        r        c        p = eval-uneval-path pat path r c p
eval-uneval-path     (right pat)      path        r        c        p = eval-uneval-path pat path r c p
eval-uneval-path     (prod lpat rpat) (inj₁ path) (r , r') (c , c') (p , p') =
  let (c'' , comp , p'') = eval-uneval-path lpat path r c p
  in  (c'' , c') , (comp >>= return refl) , (p'' , p')
eval-uneval-path (prod lpat rpat) (inj₂ path) (r , r') (c , c') (p , p') =
  let (c'' , comp , p'') = eval-uneval-path rpat path r' c' p'
  in  (c , c'') , (comp >>= return refl) , (p , p'')
eval-uneval-path     (con pat)        path        r        c        p = eval-uneval-path pat path r c p

eval-uneval :
  {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) (expr : Expr pat pat')
  (r : PatResult pat) (c : Container pat) → Consistent pat r c →
  Σ[ c' ∈ Container pat ] ((uneval pat pat' expr (eval pat pat' expr r) c ↦ c') × Consistent pat r c')
eval-uneval p var              path            r c consis = eval-uneval-path p path r c consis
eval-uneval p (k x)            expr            r c consis = c , return refl , consis
eval-uneval p (left  pat)      expr            r c consis = eval-uneval p pat expr r c consis
eval-uneval p (right pat)      expr            r c consis = eval-uneval p pat expr r c consis
eval-uneval p (prod lpat rpat) (lexpr , rexpr) r c consis =
  let (c'  , comp'  , consis' ) = eval-uneval p lpat lexpr r c  consis
      (c'' , comp'' , consis'') = eval-uneval p rpat rexpr r c' consis'
  in  c'' , (comp' >>= comp'') , consis''
eval-uneval p (con pat)        expr            r c consis = eval-uneval p pat expr r c consis

FullEmbedding-path :
  {G : U n} (pat : Pattern F G) {T : U n} (path : VarPath pat T) →
  ⟦ T ⟧ (μ F) → Container pat → Set
FullEmbedding-path var              refl        x c        = c ≡ just x
FullEmbedding-path (k _)            ()          x c
FullEmbedding-path (left  pat)      path        x c        = FullEmbedding-path pat path x c
FullEmbedding-path (right pat)      path        x c        = FullEmbedding-path pat path x c
FullEmbedding-path (prod lpat rpat) (inj₁ path) x (c , c') = FullEmbedding-path lpat path x c
FullEmbedding-path (prod lpat rpat) (inj₂ path) x (c , c') = FullEmbedding-path rpat path x c'
FullEmbedding-path (con pat)        path        x c        = FullEmbedding-path pat path x c

FullEmbedding :
  {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) (expr : Expr pat pat') →
  PatResult pat' → Container pat → Set
FullEmbedding p var              path            r        c = FullEmbedding-path p path r c
FullEmbedding p (k x)            expr            r        c = ⊤
FullEmbedding p (left  pat)      expr            r        c = FullEmbedding p pat expr r c
FullEmbedding p (right pat)      expr            r        c = FullEmbedding p pat expr r c
FullEmbedding p (prod lpat rpat) (lexpr , rexpr) (r , r') c = FullEmbedding p lpat lexpr r  c ×
                                                              FullEmbedding p rpat rexpr r' c
FullEmbedding p (con pat)        expr            r        c = FullEmbedding p pat expr r c

Extension : {G : U n} (pat : Pattern F G) → Container pat → Container pat → Set
Extension var              nothing  d        = ⊤
Extension var              (just x) d        = d ≡ just x
Extension (k x)            c        d        = ⊤
Extension (left  pat)      c        d        = Extension pat c d 
Extension (right pat)      c        d        = Extension pat c d 
Extension (prod lpat rpat) (c , c') (d , d') = Extension lpat c d × Extension rpat c' d'
Extension (con pat)        c        d        = Extension pat c d 

Extension-reflexive : 
  {G : U n} (pat : Pattern F G) (c : Container pat) → Extension pat c c
Extension-reflexive var              nothing  = tt 
Extension-reflexive var              (just _) = refl 
Extension-reflexive (k x)            c        = tt 
Extension-reflexive (left  pat)      c        = Extension-reflexive pat c 
Extension-reflexive (right pat)      c        = Extension-reflexive pat c 
Extension-reflexive (prod lpat rpat) (c , c') = Extension-reflexive lpat c , Extension-reflexive rpat c'
Extension-reflexive (con pat)        c        = Extension-reflexive pat c 

Extension-transitive : 
  {G : U n} (pat : Pattern F G) (c d e : Container pat) → Extension pat c d → Extension pat d e → Extension pat c e
Extension-transitive var         nothing  d  e  excd exde = tt
Extension-transitive var         (just x) ._ ._ refl refl = refl
Extension-transitive (k x)       c d e excd exde = tt
Extension-transitive (left  pat) c d e excd exde = Extension-transitive pat c d e excd exde
Extension-transitive (right pat) c d e excd exde = Extension-transitive pat c d e excd exde
Extension-transitive (prod lpat rpat) (c , c') (d , d') (e , e') (excd , excd') (exde , exde') =
  Extension-transitive lpat c d e excd exde , Extension-transitive rpat c' d' e' excd' exde'
Extension-transitive (con pat)   c d e excd exde = Extension-transitive pat c d e excd exde

FullEmbedding-path-Extension :
  {G : U n} (pat : Pattern F G) {T : U n} (path : VarPath pat T) →
  (x : ⟦ T ⟧ (μ F)) (c d : Container pat) →
  FullEmbedding-path pat path x c → Extension pat c d → FullEmbedding-path pat path x d
FullEmbedding-path-Extension var              refl x ._ ._ refl refl = refl
FullEmbedding-path-Extension (k _)            ()   x c d fe ex
FullEmbedding-path-Extension (left  pat)      path x c d fe ex = FullEmbedding-path-Extension pat path x c d fe ex
FullEmbedding-path-Extension (right pat)      path x c d fe ex = FullEmbedding-path-Extension pat path x c d fe ex
FullEmbedding-path-Extension (prod lpat rpat) (inj₁ path) x (c , c') (d , d') fe (ex , ex') =
  FullEmbedding-path-Extension lpat path x c d fe ex
FullEmbedding-path-Extension (prod lpat rpat) (inj₂ path) x (c , c') (d , d') fe (ex , ex') =
  FullEmbedding-path-Extension rpat path x c' d' fe ex'
FullEmbedding-path-Extension (con pat)        path x c d fe ex = FullEmbedding-path-Extension pat path x c d fe ex

FullEmbedding-Extension :
  {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) (expr : Expr pat pat') →
  (r : PatResult pat') (c c' : Container pat) →
  FullEmbedding pat pat' expr r c → Extension pat c c' → FullEmbedding pat pat' expr r c'
FullEmbedding-Extension p var              path r c c' fe ex = FullEmbedding-path-Extension p path r c c' fe ex
FullEmbedding-Extension p (k x)            expr r c c' fe ex = tt
FullEmbedding-Extension p (left  pat)      expr r c c' fe ex = FullEmbedding-Extension p pat expr r c c' fe ex
FullEmbedding-Extension p (right pat)      expr r c c' fe ex = FullEmbedding-Extension p pat expr r c c' fe ex
FullEmbedding-Extension p (prod lpat rpat) (lexpr , rexpr) (r , r') c c' (fe , fe') ex =
  FullEmbedding-Extension p lpat lexpr r c c' fe ex , FullEmbedding-Extension p rpat rexpr r' c c' fe' ex
FullEmbedding-Extension p (con pat)        expr r c c' fe ex = FullEmbedding-Extension p pat expr r c c' fe ex

uneval-path-Extension :
  {G : U n} (pat : Pattern F G) {T : U n} (path : VarPath pat T) →
  (x : ⟦ T ⟧ (μ F)) (c : Container pat) {c' : Container pat} →
  uneval-path pat path x c ↦ c' → Extension pat c c'
uneval-path-Extension var              refl x nothing  uneval-path↦ = tt
uneval-path-Extension {G} var          refl x (just y) uneval-path↦ with U-dec G x y
uneval-path-Extension {G} var          refl x (just y) (return refl) | yes _ = refl
uneval-path-Extension {G} var          refl x (just y) ()            | no  _
uneval-path-Extension (k _)            ()   x c uneval-path↦
uneval-path-Extension (left  pat)      path x c uneval-path↦ = uneval-path-Extension pat path x c uneval-path↦
uneval-path-Extension (right pat)      path x c uneval-path↦ = uneval-path-Extension pat path x c uneval-path↦
uneval-path-Extension (prod lpat rpat) (inj₁ path) x (c , c') (uneval-path↦ >>= return refl) =
  uneval-path-Extension lpat path x c uneval-path↦ , Extension-reflexive rpat c'
uneval-path-Extension (prod lpat rpat) (inj₂ path) x (c , c') (uneval-path↦ >>= return refl) =
  Extension-reflexive lpat c , uneval-path-Extension rpat path x c' uneval-path↦
uneval-path-Extension (con pat)        path x c uneval-path↦ = uneval-path-Extension pat path x c uneval-path↦

uneval-Extension :
  {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) (expr : Expr pat pat') →
  (r : PatResult pat') (c : Container pat) {c' : Container pat} →
  uneval pat pat' expr r c ↦ c' → Extension pat c c'
uneval-Extension p var              path r c uneval↦ = uneval-path-Extension p path r c uneval↦
uneval-Extension p (k x)            expr r c (return refl) = Extension-reflexive p c
uneval-Extension p (left  pat)      expr r c uneval↦ = uneval-Extension p pat expr r c uneval↦
uneval-Extension p (right pat)      expr r c uneval↦ = uneval-Extension p pat expr r c uneval↦
uneval-Extension p (prod lpat rpat) (lexpr , rexpr) (r , r') c (uneval↦ >>= uneval↦') =
  Extension-transitive p _ _ _ (uneval-Extension p lpat lexpr r  c uneval↦ )
                               (uneval-Extension p rpat rexpr r' _ uneval↦')
uneval-Extension p (con pat)        expr r c uneval↦ = uneval-Extension p pat expr r c uneval↦

uneval-path-FullEmbedding :
  {G : U n} (pat : Pattern F G) {T : U n} (path : VarPath pat T) →
  (x : ⟦ T ⟧ (μ F)) (c : Container pat) {c' : Container pat} →
  uneval-path pat path x c ↦ c' → FullEmbedding-path pat path x c'
uneval-path-FullEmbedding var         refl x nothing  (return refl) = refl
uneval-path-FullEmbedding {G} var     refl x (just y) uneval-path↦ with U-dec G x y
uneval-path-FullEmbedding var         refl x (just y) (return refl) | yes x≡y = cong just (sym x≡y)
uneval-path-FullEmbedding var         refl x (just y) ()            | no  _
uneval-path-FullEmbedding (k _)       ()   x c uneval-path↦
uneval-path-FullEmbedding (left  pat) path x c uneval-path↦ = uneval-path-FullEmbedding pat path x c uneval-path↦
uneval-path-FullEmbedding (right pat) path x c uneval-path↦ = uneval-path-FullEmbedding pat path x c uneval-path↦
uneval-path-FullEmbedding (prod lpat rpat) (inj₁ path) x (c , c') (uneval-path↦ >>= return refl) =
  uneval-path-FullEmbedding lpat path x c uneval-path↦
uneval-path-FullEmbedding (prod lpat rpat) (inj₂ path) x (c , c') (uneval-path↦ >>= return refl) =
  uneval-path-FullEmbedding rpat path x c' uneval-path↦
uneval-path-FullEmbedding (con pat  ) path x c uneval-path↦ = uneval-path-FullEmbedding pat path x c uneval-path↦

uneval-FullEmbedding :
  {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) (expr : Expr pat pat') →
  (r : PatResult pat') (c : Container pat) {c' : Container pat} →
  uneval pat pat' expr r c ↦ c' → FullEmbedding pat pat' expr r c'
uneval-FullEmbedding p var              path r c uneval↦ = uneval-path-FullEmbedding p path r c uneval↦
uneval-FullEmbedding p (k x)            expr r c uneval↦ = tt
uneval-FullEmbedding p (left  pat)      expr r c uneval↦ = uneval-FullEmbedding p pat expr r c uneval↦
uneval-FullEmbedding p (right pat)      expr r c uneval↦ = uneval-FullEmbedding p pat expr r c uneval↦
uneval-FullEmbedding p (prod lpat rpat) (lexpr , rexpr) (r , r') c (uneval↦ >>= uneval↦') =
  FullEmbedding-Extension p lpat lexpr r _ _ (uneval-FullEmbedding p lpat lexpr r  _ uneval↦ )
                                             (uneval-Extension     p rpat rexpr r' _ uneval↦') ,
  uneval-FullEmbedding p rpat rexpr r' _ uneval↦'
uneval-FullEmbedding p (con pat)        expr r c uneval↦ = uneval-FullEmbedding p pat expr r c uneval↦

fromContainer : {G : U n} (pat : Pattern F G) → Container pat → Par (PatResult pat)
fromContainer  var             (just x) = return x
fromContainer  var             nothing  = fail
fromContainer (k x)            c        = return tt
fromContainer (left  pat)      c        = fromContainer pat c
fromContainer (right pat)      c        = fromContainer pat c
fromContainer (prod lpat rpat) (c , c') = liftPar₂ _,_ (fromContainer lpat c) (fromContainer rpat c')
fromContainer (con pat)        c        = fromContainer pat c

CheckTree : {G : U n} → Pattern F G → Set
CheckTree pat = ⟦ pat ⟧ᴾ (const Bool)

runCheckTree-path : {G : U n} (pat : Pattern F G) {T : U n} → VarPath pat T → CheckTree pat → CheckTree pat
runCheckTree-path var              refl        false    = true
runCheckTree-path var              refl        true     = true
runCheckTree-path (k x)            ()          t
runCheckTree-path (left  pat)      path        t        = runCheckTree-path pat path t
runCheckTree-path (right pat)      path        t        = runCheckTree-path pat path t
runCheckTree-path (prod lpat rpat) (inj₁ path) (t , t') = runCheckTree-path lpat path t , t'
runCheckTree-path (prod lpat rpat) (inj₂ path) (t , t') = t , runCheckTree-path rpat path t'
runCheckTree-path (con pat)        path        t        = runCheckTree-path pat path t

runCheckTree : {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) →
               Expr pat pat' → CheckTree pat → CheckTree pat
runCheckTree p var              path            = runCheckTree-path p path
runCheckTree p (k x)            expr            = id
runCheckTree p (left  pat)      expr            = runCheckTree p pat expr
runCheckTree p (right pat)      expr            = runCheckTree p pat expr
runCheckTree p (prod lpat rpat) (lexpr , rexpr) = runCheckTree p rpat rexpr ∘ runCheckTree p lpat lexpr
runCheckTree p (con pat)        expr            = runCheckTree p pat expr

completeCheckTree : {G : U n} (pat : Pattern F G) → CheckTree pat → Par ⊤
completeCheckTree var              false    = fail
completeCheckTree var              true     = return tt
completeCheckTree (k x)            t        = return tt
completeCheckTree (left pat)       t        = completeCheckTree pat t
completeCheckTree (right pat)      t        = completeCheckTree pat t
completeCheckTree (prod lpat rpat) (t , t') = completeCheckTree lpat t >> completeCheckTree rpat t'
completeCheckTree (con pat)        t        = completeCheckTree pat t

empty-checkTree : {G : U n} (pat : Pattern F G) → CheckTree pat
empty-checkTree pat = defaultᴾ pat (const Bool) (const false)

completeExpr : {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) → Expr pat pat' → Par ⊤
completeExpr pat pat' expr = completeCheckTree pat (runCheckTree pat pat' expr (empty-checkTree pat))

CompleteExpr : {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) → Expr pat pat' → Set₁
CompleteExpr pat pat' expr = completeExpr pat pat' expr ↦ tt

AbsInterpCCT : {G : U n} (pat : Pattern F G) → Container pat → CheckTree pat → Set
AbsInterpCCT var              (just x) true     = ⊤
AbsInterpCCT var              (just x) false    = ⊥
AbsInterpCCT var              nothing  true     = ⊥
AbsInterpCCT var              nothing  false    = ⊤
AbsInterpCCT (k x)            c        t        = ⊤
AbsInterpCCT (left  pat)      c        t        = AbsInterpCCT pat c t
AbsInterpCCT (right pat)      c        t        = AbsInterpCCT pat c t
AbsInterpCCT (prod lpat rpat) (c , c') (t , t') = AbsInterpCCT lpat c t × AbsInterpCCT rpat c' t'
AbsInterpCCT (con pat)        c        t        = AbsInterpCCT pat c t

empty-AbsInterpCCT : {G : U n} (pat : Pattern F G) → AbsInterpCCT pat (empty-container pat) (empty-checkTree pat)
empty-AbsInterpCCT var              = tt
empty-AbsInterpCCT (k x)            = tt
empty-AbsInterpCCT (left  pat)      = empty-AbsInterpCCT pat
empty-AbsInterpCCT (right pat)      = empty-AbsInterpCCT pat
empty-AbsInterpCCT (prod lpat rpat) = empty-AbsInterpCCT lpat , empty-AbsInterpCCT rpat
empty-AbsInterpCCT (con pat)        = empty-AbsInterpCCT pat

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
uneval-AbsInterpCCT-path (left  pat)      path x c t abs comp = uneval-AbsInterpCCT-path pat path x c t abs comp
uneval-AbsInterpCCT-path (right pat)      path x c t abs comp = uneval-AbsInterpCCT-path pat path x c t abs comp
uneval-AbsInterpCCT-path (prod lpat rpat) (inj₁ path) x (c , c') (t , t') (abs , abs') (comp >>= return refl) =
  uneval-AbsInterpCCT-path lpat path x c t abs comp , abs'
uneval-AbsInterpCCT-path (prod lpat rpat) (inj₂ path) x (c , c') (t , t') (abs , abs') (comp >>= return refl) =
  abs , uneval-AbsInterpCCT-path rpat path x c' t' abs' comp
uneval-AbsInterpCCT-path (con pat)        path x c t abs comp = uneval-AbsInterpCCT-path pat path x c t abs comp

uneval-AbsInterpCCT :
  {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) (expr : Expr pat pat')
  (r : PatResult pat') (c : Container pat) (t : CheckTree pat) → AbsInterpCCT pat c t →
  {c' : Container pat} → uneval pat pat' expr r c ↦ c' → AbsInterpCCT pat c' (runCheckTree pat pat' expr t)
uneval-AbsInterpCCT p var              path r c t abs comp = uneval-AbsInterpCCT-path p path r c t abs comp
uneval-AbsInterpCCT p (k x)            expr r c t abs (return refl) = abs
uneval-AbsInterpCCT p (left  pat)      expr r c t abs comp = uneval-AbsInterpCCT p pat expr r c t abs comp
uneval-AbsInterpCCT p (right pat)      expr r c t abs comp = uneval-AbsInterpCCT p pat expr r c t abs comp
uneval-AbsInterpCCT p (prod lpat rpat) (lexpr , rexpr) (r , r') c t abs (comp >>= comp') =
  uneval-AbsInterpCCT p rpat rexpr r' _ _ (uneval-AbsInterpCCT p lpat lexpr r c t abs comp) comp'
uneval-AbsInterpCCT p (con pat)        expr r c t abs comp = uneval-AbsInterpCCT p pat expr r c t abs comp

completeCCT : {G : U n} (pat : Pattern F G) (c : Container pat) (t : CheckTree pat) →
              AbsInterpCCT pat c t → completeCheckTree pat t ↦ tt → Σ[ r ∈ PatResult pat ] (fromContainer pat c ↦ r)
completeCCT var              (just x) t        p        comp = x , return refl
completeCCT var              nothing  true     ()       comp
completeCCT var              nothing  false    p        ()
completeCCT (k x)            c        t        p        comp = tt , return refl
completeCCT (left  pat)      c        t        p        comp = completeCCT pat c t p comp
completeCCT (right pat)      c        t        p        comp = completeCCT pat c t p comp
completeCCT (prod lpat rpat) (c , c') (t , t') (p , p') (comp >>= comp') =
  let (r  , r-comp ) = completeCCT lpat c  t  p  comp
      (r' , r'-comp) = completeCCT rpat c' t' p' comp'
  in  (r , r') , (r-comp >>= r'-comp >>= return refl)
completeCCT (con pat)        c        t        p        comp = completeCCT pat c t p comp

fromContainer-consistent-complete :
  {G : U n} (pat : Pattern F G) (r : PatResult pat) (c : Container pat) →
  Consistent pat r c → {r' : PatResult pat} → fromContainer pat c ↦ r' → r ≡ r'
fromContainer-consistent-complete {G} var         r (just .r) refl (return refl) = refl
fromContainer-consistent-complete     var         r nothing   p    ()
fromContainer-consistent-complete     (k x)       r c p comp = refl
fromContainer-consistent-complete     (left  pat) r c p comp = fromContainer-consistent-complete pat r c p comp
fromContainer-consistent-complete     (right pat) r c p comp = fromContainer-consistent-complete pat r c p comp
fromContainer-consistent-complete     (prod lpat rpat) (r , r') (c , c') (p , p') (comp >>= comp' >>= return refl) =
  cong₂ _,_ (fromContainer-consistent-complete lpat r c p comp) (fromContainer-consistent-complete rpat r' c' p' comp')
fromContainer-consistent-complete     (con pat)   r c p comp = fromContainer-consistent-complete pat r c p comp

fromContainer-eval-path :
  {G : U n} (pat : Pattern F G) {T : U n} (path : VarPath pat T)
  (x : ⟦ T ⟧ (μ F)) (c : Container pat) {r : PatResult pat} →
  FullEmbedding-path pat path x c → fromContainer pat c ↦ r → eval-path pat path r ≡ x
fromContainer-eval-path var         refl x ._ refl (return refl)  = refl
fromContainer-eval-path (k _)       ()   x c  fe   fromContainer↦
fromContainer-eval-path (left  pat) path x c  fe   fromContainer↦ = fromContainer-eval-path pat path x c fe fromContainer↦
fromContainer-eval-path (right pat) path x c  fe   fromContainer↦ = fromContainer-eval-path pat path x c fe fromContainer↦
fromContainer-eval-path (prod lpat rpat) (inj₁ path) x (c , c') fe (fromContainer↦ >>= _ >>= return refl) =
  fromContainer-eval-path lpat path x c fe fromContainer↦
fromContainer-eval-path (prod lpat rpat) (inj₂ path) x (c , c') fe (_ >>= fromContainer↦ >>= return refl) =
  fromContainer-eval-path rpat path x c' fe fromContainer↦
fromContainer-eval-path (con pat)   path x c  fe   fromContainer↦ = fromContainer-eval-path pat path x c fe fromContainer↦

fromContainer-eval :
  {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) (expr : Expr pat pat')
  (r' : PatResult pat') {r : PatResult pat} (c : Container pat) →
  FullEmbedding pat pat' expr r' c → fromContainer pat c ↦ r → eval pat pat' expr r ≡ r'
fromContainer-eval p var              path x  c fe fromContainer↦ = fromContainer-eval-path p path x c fe fromContainer↦
fromContainer-eval p (k x)            expr r' c fe fromContainer↦ = refl
fromContainer-eval p (left  pat)      expr r' c fe fromContainer↦ = fromContainer-eval p pat expr r' c fe fromContainer↦
fromContainer-eval p (right pat)      expr r' c fe fromContainer↦ = fromContainer-eval p pat expr r' c fe fromContainer↦
fromContainer-eval p (prod lpat rpat) (lexpr , rexpr) (r' , r'') c (fe , fe') fromContainer↦ =
  cong₂ _,_ (fromContainer-eval p lpat lexpr r' c fe fromContainer↦)
            (fromContainer-eval p rpat rexpr r'' c fe' fromContainer↦)
fromContainer-eval p (con pat)        expr r' c fe fromContainer↦ = fromContainer-eval p pat expr r' c fe fromContainer↦
 
private

  to : {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) →
       Expr pat pat' → ⟦ G ⟧ (μ F) → Par (⟦ H ⟧ (μ F))
  to pat pat' expr = liftPar (construct pat' ∘ eval pat pat' expr) ∘ deconstruct pat
 
  from : {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) → Expr pat pat' → ⟦ H ⟧ (μ F) → Par (⟦ G ⟧ (μ F))
  from pat pat' expr = liftPar (construct pat) ∘ fromContainer pat <=<
                        flip (uneval pat pat' expr) (empty-container pat) <=< deconstruct pat'
  
  to-from-inverse :
    {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H)
    (expr : Expr pat pat') → CompleteExpr pat pat' expr →
    {x : ⟦ G ⟧ (μ F)} {y : ⟦ H ⟧ (μ F)} → to pat pat' expr x ↦ y → from pat pat' expr y ↦ x
  to-from-inverse pat pat' expr expr-complete (_>>=_ {x = r} deconstruct-pat-x↦x' (return refl)) =
    let (c' , comp' , p') = eval-uneval pat pat' expr r (empty-container pat) (empty-container-consistent pat r)
        (r' , r'-comp) = completeCCT pat c' (runCheckTree pat pat' expr (empty-checkTree pat))
                           (uneval-AbsInterpCCT pat pat' expr (eval pat pat' expr r)
                              (empty-container pat) (empty-checkTree pat) (empty-AbsInterpCCT pat) comp') expr-complete
    in  construct-deconstruct-inverse pat' _ >>= comp' >>= r'-comp >>=
        return (trans (cong (construct pat) (sym (fromContainer-consistent-complete pat r c' p' r'-comp)))
                      (deconstruct-construct-inverse pat _ deconstruct-pat-x↦x'))
  
  from-to-inverse :
    {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H)
    (expr : Expr pat pat') → CompleteExpr pat pat' expr →
    {x : ⟦ G ⟧ (μ F)} {y : ⟦ H ⟧ (μ F)} → from pat pat' expr y ↦ x → to pat pat' expr x ↦ y
  from-to-inverse pat pat' expr expr-complete (deconstruct-pat'↦ >>= uneval↦ >>= fromContainer↦ >>= return refl) =
    construct-deconstruct-inverse pat _ >>=
    return (trans (cong (construct pat')
                        (fromContainer-eval pat pat' expr _ _
                          (uneval-FullEmbedding pat pat' expr _ _ uneval↦) fromContainer↦))
                  (deconstruct-construct-inverse pat' _ deconstruct-pat'↦))

rearrangement-iso : {G : U n} (pat : Pattern F G) {H : U n} (pat' : Pattern F H) →
                    (expr : Expr pat pat') → CompleteExpr pat pat' expr → ⟦ G ⟧ (μ F) ≅ ⟦ H ⟧ (μ F)
rearrangement-iso pat pat' expr expr-complete = record
  { to   = to   pat pat' expr
  ; from = from pat pat' expr
  ; to-from-inverse = to-from-inverse pat pat' expr expr-complete
  ; from-to-inverse = from-to-inverse pat pat' expr expr-complete }
