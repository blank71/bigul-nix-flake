open import DynamicallyChecked.Universe
open import Data.Nat

module HoareLogic.Rearrangement {n : ℕ} {F : Functor n} where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens
open import DynamicallyChecked.Universe
open import DynamicallyChecked.Rearrangement
open DynamicallyChecked.Rearrangement.Components
open import HoareLogic.Semantics

open import Function
open import Data.Product
open import Data.Sum
open import Data.Fin
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


Match : {G : U n} (pat : Pattern F G) → ℙ (⟦ G ⟧ (μ F) × PatResult pat)
Match var              (x , res)                   = x ≡ res
Match (k y)            (x , res)                   = x ≡ y
Match (left  pat)      (inj₁ x , res)              = Match pat (x , res)
Match (left  pat)      (inj₂ x , res)              = ⊥
Match (right pat)      (inj₁ x , res)              = ⊥
Match (right pat)      (inj₂ x , res)              = Match pat (x , res)
Match (prod lpat rpat) ((lx , rx) , (lres , rres)) = Match lpat (lx , lres) × Match rpat (rx , rres)
Match (con pat)        (con x , res)               = Match pat (x , res)

Eval-path : {G H : U n} (pat : Pattern F G) (path : VarPath pat H) → ℙ (PatResult pat × ⟦ H ⟧ (μ F))
Eval-path var              refl (res , y)                  = res ≡ y
Eval-path (k x)            ()   (res , y)
Eval-path (left  pat)      path (res , y)                  = Eval-path pat path (res , y)
Eval-path (right pat)      path (res , y)                  = Eval-path pat path (res , y)
Eval-path (prod lpat rpat) (inj₁ path) ((lres , rres) , y) = Eval-path lpat path (lres , y)
Eval-path (prod lpat rpat) (inj₂ path) ((lres , rres) , y) = Eval-path rpat path (rres , y)
Eval-path (con pat)        path (res , y)                  = Eval-path pat path (res , y)

Eval : {G H : U n} (pat : Pattern F G) (pat' : Pattern F H) (expr : Expr pat pat') → ℙ (PatResult pat × ⟦ H ⟧ (μ F))
Eval pat var                path            (res , y)         = Eval-path pat path (res , y)
Eval pat (k x)              expr            (res , y)         = x ≡ y
Eval pat (left  pat')       expr            (res , inj₁ y)    = Eval pat pat' expr (res , y)
Eval pat (left  pat')       expr            (res , inj₂ y)    = ⊥
Eval pat (right pat')       expr            (res , inj₁ y)    = ⊥
Eval pat (right pat')       expr            (res , inj₂ y)    = Eval pat pat' expr (res , y)
Eval pat (prod lpat' rpat') (lexpr , rexpr) (res , (ly , ry)) = Eval pat lpat' lexpr (res , ly) ×
                                                                Eval pat rpat' rexpr (res , ry)
Eval pat (con pat')         expr            (res , con y)     = Eval pat pat' expr (res , y)

Rearr : {G H : U n} (pat : Pattern F G) (pat' : Pattern F H) (expr : Expr pat pat') → ℙ (⟦ G ⟧ (μ F) × ⟦ H ⟧ (μ F))
Rearr pat pat' expr = Match pat • Eval pat pat' expr

toMatch : {G : U n} (pat : Pattern F G) (x : ⟦ G ⟧ (μ F)) {res : PatResult pat} →
          deconstruct pat x ↦ res → Match pat (x , res)
toMatch     var              x        (return eq)  = eq
toMatch {G} (k y)            x        deconstruct↦ with U-dec G y x
toMatch     (k y)            x        deconstruct↦ | yes eq = sym eq
toMatch     (k y)            x        ()           | no neq
toMatch     (left  pat)      (inj₁ x) deconstruct↦ = toMatch pat x deconstruct↦
toMatch     (left  pat)      (inj₂ x) ()
toMatch     (right pat)      (inj₁ x) ()
toMatch     (right pat)      (inj₂ x) deconstruct↦ = toMatch pat x deconstruct↦
toMatch     (prod lpat rpat) (x , y)  (deconstruct-lpat↦ >>= deconstruct-rpat↦ >>= return refl) =
  toMatch lpat x deconstruct-lpat↦ , toMatch rpat y deconstruct-rpat↦
toMatch     (con pat)        (con x)  deconstruct↦ = toMatch pat x deconstruct↦

toEval-path : {G H : U n} (pat : Pattern F G) (path : VarPath pat H)
              {res : PatResult pat} → Eval-path pat path (res , eval-path pat path res)
toEval-path var              refl        = refl
toEval-path (k x)            ()
toEval-path (left  pat)      path        = toEval-path pat path
toEval-path (right pat)      path        = toEval-path pat path
toEval-path (prod lpat rpat) (inj₁ path) = toEval-path lpat path
toEval-path (prod lpat rpat) (inj₂ path) = toEval-path rpat path
toEval-path (con pat)        path        = toEval-path pat path

toEval : {G H : U n} (pat : Pattern F G) (pat' : Pattern F H) (expr : Expr pat pat')
         {res : PatResult pat} → Eval pat pat' expr (res , construct pat' (eval pat pat' expr res))
toEval pat var                path            = toEval-path pat path
toEval pat (k x)              expr            = refl
toEval pat (left  pat')       expr            = toEval pat pat' expr
toEval pat (right pat')       expr            = toEval pat pat' expr
toEval pat (prod lpat' rpat') (lexpr , rexpr) = toEval pat lpat' lexpr , toEval pat rpat' rexpr
toEval pat (con pat')         expr            = toEval pat pat' expr

toRearr : {G H : U n} (pat : Pattern F G) (pat' : Pattern F H) (expr : Expr pat pat')
          {x : ⟦ G ⟧ (μ F)} {y : ⟦ H ⟧ (μ F)} → to pat pat' expr x ↦ y → Rearr pat pat' expr (x , y)
toRearr pat pat' expr (deconstruct↦ >>= return refl) = , toMatch pat _ deconstruct↦ , toEval pat pat' expr

fromEval-path : {G H : U n} (pat : Pattern F G) (path : VarPath pat H)
                {res : PatResult pat} {y : ⟦ H ⟧ (μ F)} → Eval-path pat path (res , y) → eval-path pat path res ≡ y
fromEval-path var              refl        eval = eval
fromEval-path (k x)            ()          eval
fromEval-path (left  pat)      path        eval = fromEval-path pat path eval
fromEval-path (right pat)      path        eval = fromEval-path pat path eval
fromEval-path (prod lpat rpat) (inj₁ path) eval = fromEval-path lpat path eval
fromEval-path (prod lpat rpat) (inj₂ path) eval = fromEval-path rpat path eval
fromEval-path (con pat)        path        eval = fromEval-path pat path eval

fromMatch : {G : U n} (pat : Pattern F G) (x : ⟦ G ⟧ (μ F)) {res : PatResult pat} →
            Match pat (x , res) → deconstruct pat x ↦ res
fromMatch     var              x        match             = return match
fromMatch {G} (k y)            x        match             with U-dec G y x
fromMatch {G} (k y)            x        match             | yes eq = return refl
fromMatch {G} (k y)            x        match             | no neq with neq (sym match)
fromMatch {G} (k y)            x        match             | no neq | ()
fromMatch     (left  pat)      (inj₁ x) match             = fromMatch pat x match
fromMatch     (left  pat)      (inj₂ x) ()
fromMatch     (right pat)      (inj₁ x) ()
fromMatch     (right pat)      (inj₂ x) match             = fromMatch pat x match
fromMatch     (prod lpat rpat) (x , y)  (lmatch , rmatch) = fromMatch lpat x lmatch >>= fromMatch rpat y rmatch >>= return refl
fromMatch     (con pat)        (con x)  match             = fromMatch pat x match

fromEval : {G H : U n} (pat : Pattern F G) (pat' : Pattern F H) (expr : Expr pat pat')
           {res : PatResult pat} (y : ⟦ H ⟧ (μ F)) → Eval pat pat' expr (res , y) → construct pat' (eval pat pat' expr res) ≡ y
fromEval pat var                path            y        eval            = fromEval-path pat path eval
fromEval pat (k x)              expr            y        eval            = eval
fromEval pat (left  pat')       expr            (inj₁ y) eval            = cong inj₁ (fromEval pat pat' expr y eval)
fromEval pat (left  pat')       expr            (inj₂ y) ()
fromEval pat (right pat')       expr            (inj₁ y) ()
fromEval pat (right pat')       expr            (inj₂ y) eval            = cong inj₂ (fromEval pat pat' expr y eval)
fromEval pat (prod lpat' rpat') (lexpr , rexpr) (y , z)  (leval , reval) = cong₂ _,_ (fromEval pat lpat' lexpr y leval)
                                                                                     (fromEval pat rpat' rexpr z reval)
fromEval pat (con pat')         expr            (con y)  eval            = cong con (fromEval pat pat' expr y eval)

fromRearr : {G H : U n} (pat : Pattern F G) (pat' : Pattern F H) (expr : Expr pat pat')
            {x : ⟦ G ⟧ (μ F)} {y : ⟦ H ⟧ (μ F)} → Rearr pat pat' expr (x , y) → to pat pat' expr x ↦ y
fromRearr pat pat' expr (_ , match , eval) = fromMatch pat _ match >>= return (fromEval pat pat' expr _ eval)

rearrV-soundness :
  {S : Set} {G H : U n} (vpat : Pattern F G) (vpat' : Pattern F H) (expr : Expr vpat vpat')
  (c : CompleteExpr vpat vpat' expr) (l : S ⇆ ⟦ H ⟧ (μ F)) →
  (R : ℙ (S × PatResult vpat)) (R' : ℙ (S × S × PatResult vpat)) →
  Sound (R • Eval vpat vpat' expr) (Lens.put l)
        (λ { (s' , s , v) → ∃ λ r → R' (s' , s , r) × Eval vpat vpat' expr (r , v) }) →
  Sound (R • (Match vpat ∘ swap)) (Lens.put (l ◂ sym-iso (rearrangement-iso vpat vpat' expr c)))
        (λ { (s' , s , v) → ∃ λ r → R' (s' , s , r) × Match vpat (v , r) })
rearrV-soundness vpat vpat' expr c l R R' l-sound (s , v) (r , R-s-r , Match-v-r) =
  let v' = construct vpat' (eval vpat vpat' expr r)
      (s' , l-s-v'↦s' , r' , R'-s'-s-r' , Eval-r'-v') = l-sound (s , v') (r , R-s-r , toEval vpat vpat' expr)
  in  s' , ((fromMatch vpat v Match-v-r >>= return refl) >>= l-s-v'↦s') ,
           (r' , R'-s'-s-r' ,
            subst (λ r → Match vpat (v , r))
                         (sym (eval-injective vpat vpat' expr c
                                 (construct-injective vpat' (fromEval vpat vpat' expr v' Eval-r'-v'))))
                  Match-v-r)

rearrS-soundness :
  {V : Set} {G H : U n} (spat : Pattern F G) (tpat : Pattern F H) (expr : Expr spat tpat)
  (c : CompleteExpr spat tpat expr) (l : ⟦ H ⟧ (μ F) ⇆ V) →
  (R : ℙ (PatResult spat × V)) (R' : ℙ (PatResult spat × PatResult spat × V)) →
  Sound ((Eval spat tpat expr ∘ swap) • R) (Lens.put l)
        (λ { (t' , t , v) → ∃ λ { (r' , r) → R' (r' , r , v) × Eval spat tpat expr (r' , t') × Eval spat tpat expr (r , t) } }) →
  Sound (Match spat • R) (Lens.put (rearrangement-iso spat tpat expr c ▸ l))
        (λ { (s' , s , v) → ∃ λ { (r' , r) → R' (r' , r , v) × Match spat (s' , r') × Match spat (s , r) } })
rearrS-soundness spat tpat expr c l R R' l-sound (s , v) (r , Match-s-r , R-r-v) =
  let t = construct tpat (eval spat tpat expr r)
      (t' , l-t-v↦t' , (rr' , rr) , R'-rr'-rr-v , Eval-rr'-t' , Eval-rr-t) =
        l-sound (t , v) (r , toEval spat tpat expr , R-r-v)
  in  construct spat rr' ,
      ((fromMatch spat s Match-s-r >>= return refl) >>= l-t-v↦t' >>=
       Lens.GetPut (iso-lens (rearrangement-iso spat tpat expr c))
                   (construct-deconstruct-inverse spat rr' >>= (return (fromEval spat tpat expr t' Eval-rr'-t')))) ,
      (rr' , rr) , R'-rr'-rr-v , (toMatch spat (construct spat rr') (construct-deconstruct-inverse spat rr')) ,
      subst (λ r → Match spat (s , r))
            (sym (eval-injective spat tpat expr c (construct-injective tpat (fromEval spat tpat expr t Eval-rr-t))))
            Match-s-r
