open import DynamicallyChecked.Universe
open import Data.Nat

module HoareLogic.Completeness {n : ℕ} {F : Functor n} where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens
open import DynamicallyChecked.Case
open import DynamicallyChecked.Rearrangement
open import DynamicallyChecked.BiGUL
open import HoareLogic.Semantics
open import HoareLogic.Rearrangement
open import HoareLogic.Case
open import HoareLogic.Triple

open import Function
open import Data.Product as Product
open import Data.Bool
open import Data.Maybe
open import Data.List as List
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


skip-branch :
  {S V : U n} (bs bs' : List (CaseBranch F S V)) (cont : ⟦ S ⟧ (μ F) → Par (⟦ S ⟧ (μ F)))
  (s' s : ⟦ S ⟧ (μ F)) (v : ⟦ V ⟧ (μ F)) →
  put-with-adaptation (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F)) (interp-CaseBranch (revcat bs' bs)) [] s v cont ↦ s' →
  OutOfDomain (List.map proj₁ bs') (s , v) →
  put-with-adaptation (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F)) (interp-CaseBranch bs) (interp-CaseBranch bs') s v cont ↦ s'
skip-branch bs [] cont s' s v seq out = seq
skip-branch bs ((p , normal b q) ∷ bs') cont s' s v seq (p-s-v≡false , out)
    with skip-branch ((p , normal b q) ∷ bs) bs' cont s' s v seq out
... | c rewrite p-s-v≡false = c
skip-branch bs ((p , adaptive f) ∷ bs') cont s' s v seq (p-s-v≡false , out)
    with skip-branch ((p , adaptive f) ∷ bs) bs' cont s' s v seq out
... | c rewrite p-s-v≡false = c

project-normal-branch :
  {S V : U n} (bs bs' : List (CaseBranch F S V))
  (p : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Bool) (b : BiGUL F S V) (q : ⟦ S ⟧ (μ F) → Bool)
  (cont : ⟦ S ⟧ (μ F) → Par (⟦ S ⟧ (μ F))) (s' s : ⟦ S ⟧ (μ F)) (v : ⟦ V ⟧ (μ F)) → p s v ≡ true →
  put-with-adaptation (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F))
    (interp-CaseBranch ((p , normal b q) ∷ bs)) (interp-CaseBranch bs') s v cont ↦ s' →
  Lens.put (interp b) s v ↦ s'
project-normal-branch bs bs' p b q cont s' s v p-s-v≡true seq rewrite p-s-v≡true with seq
... | c >>= assert _ then assert _ then _ >>= return refl = c

project-adaptive-branch :
  {S V : U n} (bs bs' : List (CaseBranch F S V))
  (p : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → Bool) (f : ⟦ S ⟧ (μ F) → ⟦ V ⟧ (μ F) → ⟦ S ⟧ (μ F))
  (cont : ⟦ S ⟧ (μ F) → Par (⟦ S ⟧ (μ F))) (s' s : ⟦ S ⟧ (μ F)) (v : ⟦ V ⟧ (μ F)) → p s v ≡ true →
  put-with-adaptation (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F))
    (interp-CaseBranch ((p , adaptive f) ∷ bs)) (interp-CaseBranch bs') s v cont ↦ s' →
  cont (f s v) ↦ s'
project-adaptive-branch bs bs' p f cont s' s v p-s-v≡true c rewrite p-s-v≡true = c

mutual

  semantics-triple :
    {S V : U n} (b : BiGUL F S V) →
    Triple (λ { (s , v) → Σ[ s' ∈ ⟦ S ⟧ (μ F) ] runPar (Lens.put (interp b) s v) ≡ just s' })
           b
           (λ { (s' , s , v) → runPar (Lens.put (interp b) s v) ≡ just s' })
  semantics-triple fail = conseq (λ { (_ , ()) }) fail (λ { (() , _) })
  semantics-triple (skip {S} {V} f) =
    conseq (aux-pre ∘ toCompSeq ∘ proj₂)
           skip
           (λ { {.s , s , v} (refl , _ , eq) → fromCompSeq (aux-post (aux-pre (toCompSeq eq))) })
    where
      aux-pre : {s' s : ⟦ S ⟧ (μ F)} {v : ⟦ V ⟧ (μ F)} → Lens.put (interp (skip {S = S} {V} f)) s v ↦ s' → f s ≡ v
      aux-pre {s'} {s} {v} c with U-dec V (f s) v
      aux-pre (return refl) | yes f-s≡v = f-s≡v
      aux-pre ()            | no  _
      aux-post : {s : ⟦ S ⟧ (μ F)} {v : ⟦ V ⟧ (μ F)} → f s ≡ v → Lens.put (interp (skip {S = S} {V} f)) s v ↦ s
      aux-post {s} {v} f-s≡v with U-dec V (f s) v
      aux-post {s} {v} f-s≡v | yes _     = return refl
      aux-post {s} {v} f-s≡v | no  f-s≢v with f-s≢v f-s≡v
      aux-post {s} {v} f-s≡v | no  f-s≢v | ()
  semantics-triple replace = conseq (λ _ → tt) replace (λ { (eq , _) → cong just (sym eq) })
  semantics-triple (prod {Sl} {Vl} {Sr} {Vr} l r) =
    conseq (λ { ((sl' , sr') , eq) →
                case toCompSeq {mx = Lens.put (interp (prod l r)) _ _} eq of λ {
                  (cl >>= cr >>= return refl) → (sl' , fromCompSeq {mx = Lens.put (interp l) _ _} cl) ,
                                                (sr' , fromCompSeq {mx = Lens.put (interp r) _ _} cr) } })
           (prod (semantics-triple l) (semantics-triple r))
           (λ { ((eql , eqr) , _) →
                fromCompSeq {mx = Lens.put (interp (prod l r)) _ _} (toCompSeq eql >>= toCompSeq eqr >>= return refl) })
  semantics-triple (rearrS spat spat' expr c b) =
    conseq (λ { {s , v} (s' , eq) →
                case toCompSeq {mx = Lens.put (interp (rearrS spat spat' expr c b)) _ _} eq of λ {
                  ((deconstruct↦ >>= return refl) >>= put-b↦ >>= put-iso↦) →
                    case Iso.from-to-inverse (rearrangement-iso spat spat' expr c) put-iso↦ of λ {
                      (_ >>= return eq') → _ , toMatch spat s deconstruct↦ ,
                                           _ , trans (fromCompSeq put-b↦) (cong just (sym eq')) } } })
           (rearrS (λ { (res , v) →
                        ∃ λ res' → runPar (Lens.put (interp b) (construct spat' (eval spat spat' expr res)) v) ≡
                                     just (construct spat' (eval spat spat' expr res')) })
                   (λ { (res' , res , v) →
                        runPar (Lens.put (interp b) (construct spat' (eval spat spat' expr res)) v) ≡
                          just (construct spat' (eval spat spat' expr res')) })
                   (conseq (λ { {t , v} (res , e , res' , eq) →
                                construct spat' (eval spat spat' expr res') ,
                                subst (λ x → runPar (Lens.put (interp b) x v) ≡
                                               just (construct spat' (eval spat spat' expr res')))
                                      (fromEval spat spat' expr t e) eq })
                           (semantics-triple b)
                           (λ { {t' , t , v} (eq , res , e , res' , eq') →
                                let eq'' = cong-from-just
                                             (trans (sym (subst (λ x → runPar (Lens.put (interp b) x v) ≡
                                                                         just (construct spat' (eval spat spat' expr res')))
                                                                (fromEval spat spat' expr _ e) eq'))
                                                    eq)
                                in  (res' , res) , eq' , subst (λ x → Eval spat spat' expr (res' , x)) eq''
                                                               (toEval spat spat' expr) , e })))
           (λ { {s' , s , v} (((res' , res) , eq , m' , m) , pre) →
                fromCompSeq {mx = Lens.put (interp (rearrS spat spat' expr c b)) _ _}
                  ((fromMatch spat s m >>= return refl) >>= toCompSeq eq >>=
                   Iso.to-from-inverse (rearrangement-iso spat spat' expr c) (fromMatch spat s' m' >>= return refl)) })
  semantics-triple (rearrV vpat vpat' expr c b) =
    conseq (λ { (s' , eq) →
                case toCompSeq {mx = Lens.put (interp (rearrV vpat vpat' expr c b)) _ _} eq of λ {
                  ((deconstruct↦ >>= return refl) >>= c) → _ , (_ , fromCompSeq c) , toMatch vpat _ deconstruct↦ } })
           (rearrV (λ { (s , res) →
                        ∃ λ s' → runPar (Lens.put (interp b) s (construct vpat' (eval vpat vpat' expr res))) ≡ just s' })
                   (λ { (s' , s , res) →
                        runPar (Lens.put (interp b) s (construct vpat' (eval vpat vpat' expr res))) ≡ just s' })
                   (conseq (λ { {s , w} (res , ((s' , eq) , e)) →
                                s' , subst (λ x → runPar (Lens.put (interp b) s x) ≡ just s')
                                           (fromEval vpat vpat' expr w e) eq })
                           (semantics-triple b)
                           (λ { {s' , s , w} (eq , res , _ , e) →
                                res , subst (λ x → runPar (Lens.put (interp b) s x) ≡ just s')
                                            (sym (fromEval vpat vpat' expr _ e)) eq , e })))
           (λ { ((res , eq , m) , _) →
                fromCompSeq {mx = Lens.put (interp (rearrV vpat vpat' expr c b)) _ _}
                  ((fromMatch vpat _ m >>= return refl) >>= toCompSeq {mx = Lens.put (interp b) _ _} eq) })
  semantics-triple (case bs) = case (semantics-triple-case bs [])
                                    (λ { {sv} (s' , put-s-v≡just-s') →
                                         subst (λ ps → CaseDomain ps sv) (sym (case-main-cond-lemma bs))
                                               (inCaseDomain (interp-CaseBranch bs) [] (toCompSeq put-s-v≡just-s')) })
  
  semantics-triple-case :
    {S V : U n} (bs bs' : List (CaseBranch F S V)) →
    CaseBranchTriple
      (λ { (s , v) → Σ[ s' ∈ ⟦ S ⟧ (μ F) ] runPar (Lens.put (interp (case (revcat bs' bs))) s v) ≡ just s' })
      (λ { (s' , s , v) → runPar (Lens.put (interp (case (revcat bs' bs))) s v) ≡ just s' })
      (NormalCaseDomain (List.map (Product.map id (elimCaseBranchType (λ _ _ → true) (λ _ → false))) (revcat bs' bs)))
      bs bs'
  semantics-triple-case [] bs' = []
  semantics-triple-case {S} {V} ((p , normal b q) ∷ bs) bs' =
    conseq (λ { {s , v} ((s' , eq) , p-s-v≡true , OutOfDomain-bs'-s-v) →
                s' , fromCompSeq {mx = Lens.put (interp b) s v}
                       (project-normal-branch bs bs' p b q _ s' s v p-s-v≡true
                          (skip-branch ((p , normal b q) ∷ bs) bs' _ s' s v
                             (toCompSeq {mx = Lens.put (interp (case (revcat bs' ((p , normal b q) ∷ bs)))) s v} eq)
                             OutOfDomain-bs'-s-v)) })
           (semantics-triple b)
           (λ { {s' , s , v} (put-b-s-v≡just-s' , (s'' , put-s-v≡just-s'') , p-s-v≡true , out-s-v) →
                  Product.map fromCompSeq id
                    (aux s' s'' s v (toCompSeq put-b-s-v≡just-s') (toCompSeq put-s-v≡just-s'') p-s-v≡true out-s-v) })
      ∷ᴺ semantics-triple-case bs ((p , normal b q) ∷ bs')
    where
      aux :
        (s' s'' s : ⟦ S ⟧ (μ F)) (v : ⟦ V ⟧ (μ F)) →
        Lens.put (interp b) s v ↦ s' → Lens.put (interp (case (revcat bs' ((p , normal b q) ∷ bs)))) s v ↦ s'' →
        p s v ≡ true → OutOfDomain (List.map proj₁ bs') (s , v) →
        Lens.put (interp (case (revcat bs' ((p , normal b q) ∷ bs)))) s v ↦ s' ×
          (p s' v ≡ true × OutOfDomain (List.map proj₁ bs') (s' , v)) × (q s' ≡ true × OutOfRangeB bs' s')
      aux s' s'' s v put-b-s-v↦s' put-s-v↦s'' p-s-v≡true out-s-v
        with skip-branch ((p , normal b q) ∷ bs) bs' _ s'' s v put-s-v↦s'' out-s-v
      aux s' s'' s v put-b-s-v↦s' put-s-v↦s'' p-s-v≡true out-s-v | c rewrite p-s-v≡true with c
      aux s' s'' s v put-b-s-v↦s' put-s-v↦s'' p-s-v≡true out-s-v | _
        | put-b-s-v↦s'' >>= assert p-s'-v≡true then assert q-s'≡true then check-diversion↦ >>= return refl
        with CompSeq-deterministic put-b-s-v↦s' put-b-s-v↦s''
      aux s' .s' s v put-b-s-v↦s' put-s-v↦s' p-s-v≡true out-s-v | _
        | _ >>= assert p-s'-v≡true then assert q-s'≡true then check-diversion↦ >>= return refl | refl =
        let (outd , outr) = check-diversion-inverse (interp-CaseBranch bs') s' v check-diversion↦
        in  put-s-v↦s' , (p-s'-v≡true , subst (λ cs → OutOfDomain cs (s' , v)) (sym (case-main-cond-lemma bs')) outd) ,
                         (q-s'≡true , case-out-of-range-inverse-lemma bs' outr)
  semantics-triple-case {S} {V} ((p , adaptive f) ∷ bs) bs' =
    (λ { s v ((s' , put-s-v≡just-s') , p-s-v≡true , out-s-v) →
         let snd-seq =
               fail-continuation (⟦ S ⟧ (μ F)) (⟦ V ⟧ (μ F)) (interp-CaseBranch (revcat bs' ((p , adaptive f) ∷ bs))) []
                 (project-adaptive-branch bs bs' p f _ s' s v p-s-v≡true
                    (skip-branch ((p , adaptive f) ∷ bs) bs' _ s' s v (toCompSeq put-s-v≡just-s') out-s-v))
         in  ((s' , fromCompSeq snd-seq) ,
              subst (λ ps → NormalCaseDomain ps (f s v , v))
                    (sym (case-branch-type-lemma (revcat bs' ((p , adaptive f) ∷ bs))))
                    (inNormalCaseDomain (interp-CaseBranch (revcat bs' ((p , adaptive f) ∷ bs))) [] snd-seq)) ,
             (λ s'' put-f-s-v-v≡just-s'' →
                trans put-s-v≡just-s'
                      (cong just (CompSeq-deterministic snd-seq (toCompSeq put-f-s-v-v≡just-s'')))) })
      ∷ᴬ semantics-triple-case bs ((p , adaptive f) ∷ bs')

completeness :
  {S V : U n} {R : ℙ (⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} (b : BiGUL F S V) {R' : ℙ (⟦ S ⟧ (μ F) × ⟦ S ⟧ (μ F) × ⟦ V ⟧ (μ F))} →
  Sound R (Lens.put (interp b)) R' → Triple R b R'
completeness b {R'} sound =
  conseq (λ {sv} r → Product.map id (fromCompSeq ∘ proj₁) (sound sv r))
         (semantics-triple b)
         (λ { {s' , s , v} (put-s-v≡just-s' , R-s-v) →
              let (s'' , put-s-v↦s'' , R'-s''-s-v) = sound (s , v) R-s-v
              in  subst (λ x → R' (x , s , v))
                        (cong-from-just (trans (sym (fromCompSeq put-s-v↦s'')) put-s-v≡just-s'))
                        R'-s''-s-v })
