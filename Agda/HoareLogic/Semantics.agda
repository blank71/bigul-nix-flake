module HoareLogic.Semantics where

open import DynamicallyChecked.Utilities
open import DynamicallyChecked.Partiality
open import DynamicallyChecked.Lens
open import DynamicallyChecked.Universe
open import DynamicallyChecked.Rearrangement
open import DynamicallyChecked.BiGUL

open import Function
open import Data.Product as Product
open import Data.Sum
open import Data.Bool
open import Data.List
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality


ℙ : Set → Set₁
ℙ A = A → Set

_⊆_ : {A : Set} → ℙ A → ℙ A → Set
S ⊆ T = ∀ {a} → S a → T a

infix 2 _⊆_

∅ : {A : Set} → ℙ A
∅ _ = ⊥

Π : {A : Set} → ℙ A
Π _ = ⊤

True : ℙ Bool
True b = b ≡ true

False : ℙ Bool
False b = b ≡ false

_∪_ : {A : Set} → ℙ A → ℙ A → ℙ A
(S ∪ T) a = S a ⊎ T a

infixr 3 _∪_

_∩_ : {A : Set} → ℙ A → ℙ A → ℙ A
(S ∩ T) a = S a × T a

infixr 3 _∩_

_⇒_ : {A B : Set} → ℙ (A × B) → ℙ (A × B) → ℙ (A × B)
(R ⇒ S) (a , b) = R (a , b) → S (a , b)

_⋈_ : {A B C : Set} → ℙ (A × B) → ℙ (A × C) → ℙ (A × B × C)
(R ⋈ S) (a , b , c) = R (a , b) × S (a , c)

∑ : {A B : Set} → ℙ (A × B) → ℙ B
∑ R b = ∃ λ a → R (a , b) 

_•_ : {A B C : Set} → ℙ (A × B) → ℙ (B × C) → ℙ (A × C)
R • S = ∑ ((R ∘ swap) ⋈ S)

Sound : {S V : Set} → ℙ (S × V) → (S → V → Par S) → ℙ (S × S × V) → Set₁
Sound {S} {V} R f R' = (sv : S × V) → let (s , v) = sv in R (s , v) → Σ[ s' ∈ S ] ((f s v ↦ s') × R' (s' , s , v))

consequence : {S V : Set} (R : ℙ (S × V)) (f : S → V → Par S) (R' : ℙ (S × S × V)) → Sound R f R' →
              (Q : ℙ (S × V)) → Q ⊆ R → (Q' : ℙ (S × S × V)) → R' ∩ (Q ∘ proj₂) ⊆ Q' → Sound Q f Q'
consequence R f R' sound Q Q⊆R Q' R'∩Q∘proj₂⊆Q' (s , v) Q-s-v =
  let (s' , f-s-v↦s' , R'-s'-s-v) = sound (s , v) (Q⊆R Q-s-v) in s' , f-s-v↦s' , R'∩Q∘proj₂⊆Q' (R'-s'-s-v , Q-s-v)

partial-forward-consistency :
  {S V : Set} (R : ℙ (S × V)) (l : S ⇆ V) (R' : ℙ (S × V)) →
  Sound R (Lens.put l) (R' ∘ Product.map id proj₂) →
  {s : S} {v : V} → Lens.get l s ↦ v → (R ⇒ R') (s , v)
partial-forward-consistency R l R' sound get↦ Rsv with sound _ Rsv
partial-forward-consistency R l R' sound get↦ Rsv | (s' , put↦ , R's'v) with CompSeq-deterministic put↦ (Lens.GetPut l get↦)
partial-forward-consistency R l R' sound get↦ Rsv | (s' , put↦ , R's'v) | refl = R's'v

hippocratic-triple : {S V : Set} (R : ℙ (S × V)) (l : S ⇆ V) →
                     Sound R (Lens.put l) (uncurry _≡_ ∘ Product.map id proj₁) →
                     (s : S) (v : V) → R (s , v) → Lens.get l s ↦ v
hippocratic-triple R l sound s v Rsv with sound (s , v) Rsv
hippocratic-triple R l sound s v Rsv | .s , put↦ , refl = Lens.PutGet l put↦

fail-soundness : {S V : Set} → Sound {S} {V} ∅ (Lens.put (iso-lens empty-iso)) ∅
fail-soundness _ ()

skip-soundness : {S V : Set} (_≟_ : Decidable (_≡_ {A = V})) (f : S → V) →
                 Sound (uncurry _≡_ ∘ Product.map f id) (Lens.put (skip-lens _≟_ f)) (uncurry _≡_ ∘ Product.map id proj₁)
skip-soundness _≟_ f (s , v) f-s≡v with f s ≟ v
skip-soundness _≟_ f (s , v) f-s≡v | yes _     = s , return refl , refl
skip-soundness _≟_ f (s , v) f-s≡v | no  f-s≢v with f-s≢v f-s≡v
skip-soundness _≟_ f (s , v) f-s≡v | no  f-s≢v | ()

replace-soundness : {A : Set} → Sound Π (Lens.put (iso-lens (id-iso {A}))) (uncurry _≡_ ∘ Product.map id proj₂)
replace-soundness (s , v) _ = v , return refl , refl

prod-soundness : {A B C D : Set}
                 (R : ℙ (A × C)) (R' : ℙ (A × A × C)) (l : A ⇆ C) → Sound R (Lens.put l) R' →
                 (S : ℙ (B × D)) (S' : ℙ (B × B × D)) (r : B ⇆ D) → Sound S (Lens.put r) S' →
                 Sound (λ { ((a , b) , (c , d)) → R (a , c) × S (b , d) }) (Lens.put (l ↕ r))
                       (λ { ((a' , b') , (a , b) , (c , d)) → R' (a' , a , c) × S' (b' , b , d) })
prod-soundness R R' l l-sound S S' r r-sound ((a , b) , (c , d)) (R-a-c , S-b-d) =
  let (a' , l-a-c↦a' , R'-a'-a-c) = l-sound (a , c) R-a-c
      (b' , r-b-d↦b' , S'-b'-b-d) = r-sound (b , d) S-b-d
  in  (a' , b') , (l-a-c↦a' >>= r-b-d↦b' >>= return refl) , (R'-a'-a-c , S'-b'-b-d)

dep-soundness : {S V V' : Set} (f : V → V') (dec : Decidable {A = V'} _≡_) (l : S ⇆ V)
                (R : ℙ (S × (V × V'))) (R' : ℙ (S × S × (V × V'))) →
                Sound (R ∘ Product.map id < id , f >) (Lens.put l) (R' ∘ Product.map id (Product.map id < id , f >)) →
                Sound ((uncurry _≡_ ∘ Product.map f id ∘ proj₂) ∩ R) (Lens.put (l ◂ sym-iso (dependency-iso f dec))) R'
dep-soundness f dec l R R' l-sound (s , (v , .(f v))) (refl , R-s-v-fv) with dec (f v) (f v)
dep-soundness f dec l R R' l-sound (s , (v , .(f v))) (refl , R-s-v-fv) | yes _ =
  Product.map id (Product.map (return refl >>=_) id) (l-sound (s , v) R-s-v-fv)
dep-soundness f dec l R R' l-sound (s , (v , .(f v))) (refl , R-s-v-fv) | no neq with neq refl
dep-soundness f dec l R R' l-sound (s , (v , .(f v))) (refl , R-s-v-fv) | no neq | ()

SoundG : {S V : Set} → ℙ S → (S → Par V) → ℙ (S × V) → Set₁
SoundG {S} {V} P g R = (s : S) → P s → Σ[ v ∈ V ] g s ↦ v × R (s , v)

consequenceG : {S V : Set} (P : ℙ S) (g : S → Par V) (R : ℙ (S × V)) → SoundG P g R →
               (Q : ℙ S) → Q ⊆ P → (T : ℙ (S × V)) → R ∩ (Q ∘ proj₁) ⊆ T → SoundG Q g T
consequenceG P g R soundR Q Q⊆P T R∩Q⊆T s qs = let (v , g-s↦v , Rsv) = soundR s (Q⊆P qs)
                                               in   v , g-s↦v , R∩Q⊆T (Rsv , qs)

range-interpretation-r :
  {S V : Set} (P : ℙ S) (l : S ⇆ V) (R : ℙ (S × V)) →
  SoundG P (Lens.get l) R →
  ((s' : S) → P s' → Σ[ s ∈ S ] Σ[ v ∈ V ] Lens.put l s v ↦ s' × R (s , v)) ×
  ((s : S) (v : V) → P s → Lens.get l s ↦ v → R (s , v))
range-interpretation-r P l R soundG =
  (λ s' Ps' → let (v , get-l-s'↦v , Rs'v) = soundG s' Ps'
              in  s' , v , Lens.GetPut l get-l-s'↦v , Rs'v) ,
  (λ s v Ps get-l-s↦v → let (v' , get-l-s↦v' , Rsv') = soundG s Ps
                        in  subst (R ∘ (_,_ s)) (CompSeq-deterministic get-l-s↦v' get-l-s↦v) Rsv')

range-interpretation-l :
  {S V : Set} (P : ℙ S) (l : S ⇆ V) (R : ℙ (S × V)) →
  ((s' : S) → P s' → Σ[ s ∈ S ] Σ[ v ∈ V ] Lens.put l s v ↦ s' × R (s , v)) →
  ((s : S) (v : V) → P s → Lens.get l s ↦ v → R (s , v)) →
  SoundG P (Lens.get l) R
range-interpretation-l P l R range side s Ps with range s Ps
range-interpretation-l P l R range side s Ps | s' , v , put-l-s'-v↦s , Rs'v =
  let get-l-s↦v = Lens.PutGet l put-l-s'-v↦s
  in  v , get-l-s↦v , side s v Ps get-l-s↦v

total-forward-consistency :
  {S V : Set} (R : ℙ (S × V)) (l : S ⇆ V) (R' : ℙ (S × V)) (P : ℙ S) →
  Sound R (Lens.put l) (R' ∘ Product.map id proj₂) → SoundG P (Lens.get l) R →
  (s : S) → P s → Σ[ v ∈ V ] Lens.get l s ↦ v × R' (s , v)
total-forward-consistency R l R' P sound soundG s Ps with soundG s Ps
total-forward-consistency R l R' P sound soundG s Ps | v , get↦ , Rsv with sound (s , v) Rsv
total-forward-consistency R l R' P sound soundG s Ps | v , get↦ , Rsv | s' , put↦ , R's'v
  with CompSeq-deterministic put↦ (Lens.GetPut l get↦)
total-forward-consistency R l R' P sound soundG s Ps | v , get↦ , Rsv | .s , put↦ , R'sv | refl = v , get↦ , R'sv

fail-soundnessG : {S V : Set} → SoundG {S} {V} ∅ (Lens.get (iso-lens empty-iso)) ∅
fail-soundnessG _ ()

skip-soundnessG : {S V : Set} (_≟_ : Decidable (_≡_ {A = V})) (f : S → V) →
                  SoundG Π (Lens.get (skip-lens _≟_ f)) (uncurry _≡_ ∘ Product.map f id)
skip-soundnessG _≟_ f s _ = f s , return refl , refl

replace-soundnessG : {A : Set} → SoundG Π (Lens.get (iso-lens (id-iso {A}))) (uncurry _≡_)
replace-soundnessG x _ = x , return refl , refl

prod-soundnessG : {A B C D : Set}
                  (P : ℙ A) (R : ℙ (A × C)) (l : A ⇆ C) → SoundG P (Lens.get l) R →
                  (Q : ℙ B) (S : ℙ (B × D)) (r : B ⇆ D) → SoundG Q (Lens.get r) S →
                  SoundG (λ { (a , b) → P a × Q b }) (Lens.get (l ↕ r))
                         (λ { ((a , b) , (c , d)) → R (a , c) × S (b , d) })
prod-soundnessG P R l l-sound Q S r r-sound (a , b) (Pa , Qb) =
  let (c , get-l-a↦c , Rac) = l-sound a Pa
      (d , get-r-b↦d , Sbd) = r-sound b Qb
  in  (c , d) , (get-l-a↦c >>= get-r-b↦d >>= return refl) , (Rac , Sbd)

dep-soundnessG : {S V V' : Set} (f : V → V') (dec : Decidable {A = V'} _≡_) (l : S ⇆ V)
                 (P : ℙ S) (R : ℙ (S × (V × V'))) →
                 SoundG P (Lens.get l) (R ∘ Product.map id < id , f >) →
                 SoundG P (Lens.get (l ◂ sym-iso (dependency-iso f dec))) ((uncurry _≡_ ∘ Product.map f id ∘ proj₂) ∩ R)
dep-soundnessG f dec l P R l-sound s Ps =
  let (v , get-l-s↦v , R-s-v-fv) = l-sound s Ps
  in  (v , f v) , (get-l-s↦v >>= return refl) , (refl , R-s-v-fv)

composition-soundness :
  {A B C : Set} (l : A ⇆ B) (r : B ⇆ C)
  (R : ℙ (A × C)) (P : ℙ A) (R' : ℙ (A × B)) (T' : ℙ (A × A × B)) (U' : ℙ (B × B × C)) →
  let Pre-l : ℙ (A × B)
      Pre-l = λ { (a , b') → Σ[ b ∈ B ] Σ[ c ∈ C ] R (a , c) × R' (a , b) × U' (b' , b , c) }
  in  Sound Pre-l (Lens.put l) (λ { (a' , a , b) → R' (a' , b) × T' (a' , a , b)}) → SoundG P (Lens.get l) Pre-l →
      Sound (λ { (b , c) → Σ[ a ∈ A ] R' (a , b) × R (a , c) }) (Lens.put r) U' →
      Sound (R ∩ (P ∘ proj₁)) (Lens.put (l ↔ r))
            (λ { (a' , a , c) → Σ[ b ∈ B ] Σ[ b' ∈ B ] T' (a' , a , b') × U' (b' , b , c) })
composition-soundness l r R P R' T' U' l-sound l-soundG r-sound (a , c) (Rac , Pa)
  with total-forward-consistency _ l R' P
         (consequence _ (Lens.put l) _ l-sound _ id (λ { (a' , _ , b) → R' (a' , b) }) (proj₁ ∘ proj₁)) l-soundG a Pa
composition-soundness l r R P R' T' U' l-sound l-soundG r-sound (a , c) (Rac , Pa)
  | b , get-l-a↦b , R'ab with r-sound (b , c) (a , R'ab , Rac)
composition-soundness l r R P R' T' U' l-sound l-soundG r-sound (a , c) (Rac , Pa)
  | b , get-l-a↦b , R'ab | b' , put-r-b-c↦b' , U'b'bc with l-sound (a , b') (b , c , Rac , R'ab , U'b'bc)
composition-soundness l r R P R' T' U' l-sound l-soundG r-sound (a , c) (Rac , Pa)
  | b , get-l-a↦b , R'ab | b' , put-r-b-c↦b' , U'b'bc | a' , put-l-a-b'↦a' , R'a'b' , T'a'ab' =
  a' , (get-l-a↦b >>= put-r-b-c↦b' >>= put-l-a-b'↦a') , b , b' , T'a'ab' , U'b'bc
