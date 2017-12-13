module Everything where

import DynamicallyChecked.Utilities
import DynamicallyChecked.Partiality
import DynamicallyChecked.Lens
import DynamicallyChecked.Universe
import DynamicallyChecked.Rearrangement
import DynamicallyChecked.Case
import DynamicallyChecked.BiGUL
import DynamicallyChecked.Examples.Bookstore
import HoareLogic.Utilities
import HoareLogic.Semantics
import HoareLogic.Rearrangement
import HoareLogic.Case
import HoareLogic.Triple
import HoareLogic.Completeness
import HoareLogic.Examples.Alignment
import HoareLogic.Examples.Miscellaneous
import HoareLogic.Examples.ReplaceAll


--------
-- Section 2

Definition-2·1 = DynamicallyChecked.BiGUL.BiGUL
---
---  The type of BiGUL programs depends on a universe of mutually recursive polynomial types:
---
_ =    DynamicallyChecked.Universe.U
---
---  The put semantics of a BiGUL program is extracted as follows. First we interpret the program
---  as a well-behaved lens of type:
---
_ =    DynamicallyChecked.Lens.Lens
---
---  using the interpreter:
---
_ =    DynamicallyChecked.BiGUL.interp
---
---  We can then extract a put function from the lens using the projection function:
---
_ =    DynamicallyChecked.Lens.Lens.put
---
---  Finally, the return type of the put function is wrapped inside the Par type constructor
---  (see Section 2 of the BiGUL paper at PEPM 2016: https://doi.org/10.1145/2847538.2847544),
---  which can be turned into Maybe using:
---
_ =    DynamicallyChecked.Partiality.runPar
---
---  The get semantics is similar.
---

Theorem-2·2-PutGet = DynamicallyChecked.Lens.Lens.PutGet
Theorem-2·2-GetPut = DynamicallyChecked.Lens.Lens.GetPut
---
---  Since, as shown for Definition 2.1, every BiGUL program is interpreted as a Lens,
---  in which these two proofs are mandatory, the put and get semantics of any BiGUL
---  program are necessarily well-behaved.
---
---  We could read Par as a synonym of Maybe, and understand a type mx ↦ x in the
---  well-behavedness statements as mx ≡ just x. Formally, the type constructor
---
_ =    DynamicallyChecked.Partiality._↦_
---
---  is a shorthand for
---
_ =    DynamicallyChecked.Partiality.CompSeq
---
---  and the equivalence between CompSeq mx x and runPar mx ≡ just x is witnessed by:
---
_ =    DynamicallyChecked.Partiality.fromCompSeq
_ =    DynamicallyChecked.Partiality.toCompSeq
---
---  Again, see Section 2 of the PEPM 2016 paper for more detail.
---

Lemma-2·3 = DynamicallyChecked.Lens.uniqueness


--------
-- Section 3

Notation-3·1 = HoareLogic.Semantics.ℙ

Definition-3·2 = HoareLogic.Triple.Triple
---
---  For the preconditions and postconditions, we exploit the fact that relations are
---  just Set-valued functions and specify them using functional notations. For example,
---  the precondition for replace
---
_ =    HoareLogic.Semantics.Π
---
---  is the constant function always returning the unit type ⊤, and the postcondition
---  is expanded as follows:
---
---      uncurry _≡_ ∘ Product.map id proj₁
---    = λ { (s' , s , v) → uncurry _≡_ (Product.map id proj₁ (s' , s , v)) }
---    = λ { (s' , s , v) → uncurry _≡_ (s' , s) }
---    = λ { (s' , s , v) → s' ≡ s }
---
---  where the use of the anonymous λ-expressions directly correspond to the comprehension
---  relation syntax (Notation 3.4) used in the paper. We can, of course, directly use
---  anonymous λ-expressions to specify relations, as done in the prod rule, for example.
---
---  The rearrangement rules presented in the paper rely essentially on pattern-matching
---  comprehension relations, and non-linear patterns can appear in these relations.
---  We cannot simply use anonymous λ-expressions to model them since non-linear patterns
---  are not allowed. Below is an account of how we circumvented the problem. We build on
---  the formalisation of pattern matching in the PEPM 2016 paper (Section 3.2):
---
_ =    DynamicallyChecked.Universe.PatternMatching.pat-iso
---
---  To avoid going into the detail, below we will give a simplified account, hiding all
---  parameters and indices. Suppose that we are rearranging the view from vpat for type V
---  to wpat for type W. We first defines a type:
---
_ =    DynamicallyChecked.Universe.PatternMatching.PatResult
---
---  An inhabitant of PatResult is the result of matching a value of type V with vpat, and
---  can be thought of as a mapping from every variable in vpat to the component matching
---  the variable. Two relations are then defined:
---
_ =    HoareLogic.Rearrangement.Match
---
---  which can be thought to have the simplified type P(V × PatResult)), relates v : V and
---  r : PatResult if and only if v matches vpat and r is the result of the matching
---  (as witnessed by:
---
_ =    HoareLogic.Rearrangement.fromMatch
_ =    HoareLogic.Rearrangement.toMatch
---
---  ), and
---
_ =    HoareLogic.Rearrangement.Eval
---
---  which has the simplified type P(PatResult × W), relates r : PatResult and w : W if and
---  only if w is the result of evaluating wpat (as an expression) using r as the environment
---  (witnessed by:
---
_ =    HoareLogic.Rearrangement.fromEval
_ =    HoareLogic.Rearrangement.toEval
---
---  ) With these two relations, we state the precondition for the whole rearrV program as
---
---    < s v | ∃r. Match v r ∧ R s r >
---
---  and the precondition for the inner program as
---
---    < s w | ∃r. Eval r w ∧ R s r >
---
---  making no use of (non-linear) pattern-matching comprehension relations.
---

Theorem-3·3-⇒ = HoareLogic.Triple.soundness
Theorem-3·3-⇐ = HoareLogic.Completeness.completeness
---
---  Soundness is proved by induction as usual, and completeness is proved mainly by showing
---  that a triple about the exact put semantics can be derived:
---
_ =    HoareLogic.Completeness.semantics-triple
---
---  which, in the paper's notation, is:
---
---    { s v | ∃s'. put b s v = just s' }  b  { s' s v | put b s v = just s' }
---
---  for any BiGUL program b. Completeness is then a corollary: Suppose that the right-hand
---  side of Theorem 3.3 holds. Then the precondition R implies that of the above triple,
---  whose postcondition, together with R, implies the desired postcondition R'.

Theorem-3·8 = HoareLogic.Semantics.partial-forward-consistency
---
---  We do not use the definition of graphs (Definition 3.7) in the formalisation
---  due to size issues. All references to graphs are expanded inline.
---


--------
-- Section 4

Example-4·1 = HoareLogic.Examples.Miscellaneous.replace²-correctness

Section-4·3-example = HoareLogic.Examples.Miscellaneous.replace²-equal-view-correctness
---
---  The postcondition proved is stronger than that in the paper.
---  In the comprehension relation notation:
---
---    < (s' , t') _ (v , w) | s' = t' ∧ (s' , t') = (v , w) >
---

Example-4·2 = HoareLogic.Examples.Miscellaneous.keepHeight-correctness
---
---  The formalisation provides a correct-by-construction but very cryptic way of
---  writing rearranging λ-expressions, as can be seen, e.g., in the definition
---  of keepHeight:
---
_ =    HoareLogic.Examples.Miscellaneous.keepHeight
---
---  The Haskell port of BiGUL allows the programmer to write ordinary λ-expressions
---  in rearragements, and uses Template Haskell to check the invertibility constraints
---  and generate the actual code.
---  

Example-4·3 = HoareLogic.Examples.Miscellaneous.eqCheck-correctness

Example-4·4 = HoareLogic.Examples.Miscellaneous.resetHeight-correctness

Example-4·5-i  = HoareLogic.Examples.Miscellaneous.emb-correctness
Example-4·5-ii = HoareLogic.Examples.Miscellaneous.emb-correctness'


--------
-- Section 5

alwaysResetHeight-putback-triple = HoareLogic.Examples.Miscellaneous.alwaysResetHeight-correctness

Definition-5·1 = HoareLogic.Triple.TripleR

Theorem-5·2-⇒ = HoareLogic.Triple.soundnessR
Theorem-5·2-⇐ = HoareLogic.Completeness.completenessR
---
---  The proofs are analogous to those of Theorem 3.3
---

Lemma-5·3-⇒ = HoareLogic.Semantics.range-interpretation-r
Lemma-5·3-⇐ = HoareLogic.Semantics.range-interpretation-l

Theorem-5·4 = HoareLogic.Semantics.total-forward-consistency

Example-5·5 = HoareLogic.Examples.Miscellaneous.emb-range

Example-5·6 = HoareLogic.Examples.Miscellaneous.alwaysResetHeight-range


--------
-- Section 6

Theorem-6·1 = HoareLogic.Triple.expandTriple

Theorem-6·2 = HoareLogic.Triple.expandTripleR


--------
-- Section 7

keyAlign-putback-triple = HoareLogic.Examples.Alignment.keyAlign-correctness
---
---  The datatypes of source and view lists need to be encoded in the universe so that
---  we can write BiGUL programs operating on them:
---
_ =    HoareLogic.Examples.Alignment.F
---
---  In general, the set of all datatypes to be processed by a BiGUL program needs to be
---  fixed in advance and encoded as a base functor, on which the type of the BiGUL program
---  depends.
---
---  As mentioned in the paper, the actually verified key-based alignment program
---
_ =    HoareLogic.Examples.Alignment.keyAlignᴮ
---
---  is only the (non-recursive) body of keyAlign in Figure 4, and the auxiliary function
---
_ =    HoareLogic.Examples.Alignment.extract
---
---  includes some redundant branches to pass Agda's totality check. Also different from
---  Figure 4 are some uses of Agda-specific programming patterns, like using the 'any'
---  function in the standard library
---
import Data.List.Any using (any)
---
---  to specify the main condition of the fourth branch. Such modifications help to make
---  it easier to obtain proofs of properties needed in the derivation of the triple.
---

keyAlign-range-triple = HoareLogic.Examples.Alignment.keyAlign-range


--------
-- Section 8

soundness-of-composition-rule = HoareLogic.Semantics.composition-soundness

replaceAll-putback-triple = HoareLogic.Examples.ReplaceAll.replaceAll-correctness
replaceAll-range-triple   = HoareLogic.Examples.ReplaceAll.replaceAll-range
