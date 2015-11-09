Dear Hsiang-Shang,

   Below please find reviews for your submission
BiGUL: A Formally Verified Core Language for Putback-Based Bidirectional Programming.

   I sincerely hope that these reviews can help you with the next step in your research project and the 
production of a revised paper.

   As I mentioned in the previous email, APLAS 2015 has a poster session (see 
<http://pl.postech.ac.kr/aplas2015/?page_id=150>). Please consider submitting a poster. Hope to see 
you in Pohang in November.

Best regards,

Xinyu


----------------------- REVIEW 1 ---------------------
PAPER: 46
TITLE: BiGUL: A Formally Verified Core Language for Putback-Based Bidirectional Programming
AUTHORS: Hsiang-Shang Ko, Tao Zan and Zhenjiang Hu

OVERALL EVALUATION: 1 (weak accept)
REVIEWER'S CONFIDENCE: 4 (high)

----------- REVIEW -----------
Summary

Bidirectional transformations (bx) are transformations that can be read either in a forward direction ("get") mapping some source data to a view, or backward ("put"), and the backward direction can look at the previous version of the source and merge it with the view (in contrast to, say, an invertible function that can only recompute the source from the view).  Some of the authors and others have previously advocated a so-called "putback-based" approach to this, contrary to previous work that (in the authors' view) overemphasizes the get direction.  In this paper, the authors present a core language, formalized in Agda (with appropriate bx laws proved) for bidirectional transformations following this approach, and intended as a rational reconstruction of some recent work on bidirectional transformations for XML updates and parsing.  

The paper first introduces an Agda type that includes the get and put functions and axioms stating their well-behavedness, formalized via a "partial computation" datatype that has the operations of a monad with "failure" (it doesn't satisfy the laws of a monad, but there is a natural mapping to the usual Maybe monad).  The reason for this setup is to smooth the proofs of correctness, and the proof of correctness of composition is used to illustrate this. Next the paper presents BiGUL, a core language defined as another Agda datatype.  The semantics of its operations are discussed and presented via high-level exposition and examples.  These are defined and proved correct in the accompanying Agda code, and include operations like alignment of lists, case analysis on the source and case analysis of the view (similar to those presented in recent papers, but which have not been formalized and proved correct previously to the best of my knowledge.)

Evaluation

I have some doubts about the putback-based approach (which haven't been relieved by previous papers on this approach and aren't addressed here either).  It seems to me that the approach the authors take here (and introduce in previous work advocating "putback-based" bx) is not formally different from the get/put lens framework that has already been studied extensively.  What is different is the language constructs/combinators and how they are used, and it is unclear how calling them "putback-based" and encouraging programmers to think about writing the put direction helps; at least, I still find it difficult to follow transformations written in this style, and would appreciate a clearer explanation of why this approach is better than how one would write similar examples in a so-called "get-based" language, or a clearer explanation why such examples are impossible.

That said, I think this submission makes a number of interesting contributions that don't hinge on the merits of the putback-based approach: these include formalization of correctness and well-behavedness properties of BXs (mostly) in Agda, including development of techniques for defining bxs using pattern-matching and partial isomorphisms.  I also found the use of the Par (pre)monad to represent computations (and importantly, to allow Agda to inspect and simplify types in a way that aids typechecking/proof) to be interesting and it may be a technique that finds other applications in this area or in reasoning about monadic computations in Agda.

At the risk of committing the sin of telling the authors that they should have written a different paper, I would venture to suggest that the paper would be better if it dropped the discussion of putback-based BX entirely and focused on these other contributions; I think the work involved in formalizing a realistic core language for BX (whether or not it is "putback-based") is an original and significant contribution in its own right, and I think the paper can be accepted on that basis.  The impact of this aspect of the contribution could be increased by including more "standard" combinators in the get-based style in the formalization (or clarifying that they are definable).

Correctness, of course, rests on the validity of the Agda code, which I unfortunately haven't been able to check using Agda 2.4.2, and the authors don't state which version of Agda should be used.


Detailed comments 


p1. "Most [BX approaches ask the programmer to write get], and derive a backward put for free."  This is not entirely accurate, and gives the impression that techniques where the programmer writes both directions using constructs from which both directions can be derived (which is essentially the approach taken in this paper too) are little-investigated, which is not the case.

p1. "more than one incomparable puts for a get [4]" Citation [4] seems to be an unrelated paper that doesn't discuss this issue.

p2. "completely formally verified" - meaning well-behavedness is verified in Agda?  or does "complete" refer to any other properties?

p2. "two folds" -> "twofold"

p3.  Comparing to [22], it might be helpful to mention that the arbitrary monad parameter allowed there is not present here, and this formulation also doesn't consider initialization.

p4. "are actually total functions [of type] A -> Maybe A"  this seems not to be the case; Par has a lot more structure than Maybe.  

p4. "not possible in the setting of complete partial orders" - at least when we consider the bottom value to be "nontermination" which is not observable.

p4. "proofs that each"  -> "prove that each"

p4.  Despite the use of monadic notation, Par is not itself a monad (it doesn't satisfy the laws exactly, since for example return x >>= id is a term that's not literally equal to return x.)  Please clarify this.

p5. What does the underscore in the definition of (mx >>= f) |-> y mean?

p6. Lens.get l a' b' and Lens.get r b' c are missing \mapsto's


p6, "putback is the essence" theorem.  It wasn't clear if this is proved formally (i.e. if the theorem holds constructively, so that the get/put and putback-oriented lens definitions are constructively equivalent).  Moreover, it is unclear to what extent the approach in this paper supports the claim that the "putback"-oriented approach is better.


p5-6.  The discussion shows that composition (and presumably other operations) preserves the enriched forms of the laws (using Par) built into the lenses defined on page 2.  However, the relationship between these and a conventional definition (e.g. based on ordinary partial functions A -> Maybe B) should be established,  to cement the connection to other approaches to BX.

p5-6.  Why aren't Agda's built-in proof terms for equality proofs enough?  It seems that they ought to suffice, but the approach taken here helps with automation of proofs.  Why wouldn't this reasoning work using conventional partial functions A -> Maybe B (viewing mx |-> x as shorthand for runPar mx = just x)?  Or if it would work,  but the reasoning is more complicated, can you illustrate why?

p7. In figure 1, please explain where Pattern, BiGULs and Paths types are defined (not until later or in some cases not in the paper at all)

p7.  fig. 1, type of "rearr" - why is the result type BiGUL S V -> BiGUL S V' instead of BiGUL V V" (seems like the latter should be definable from the former)

p7.  In a dependently typed language, one could imagine using types to express the domains of "partial" operations more precisely so that they become total.    I wasn't sure why this approach is taken as opposed to reasoning about partial operations intensionally using Par.  This is discussed as an area of future work later in the paper; it would be helpful to clarify whether there is an obvious obstacle to this approach or it just hadn't been tried yet.  Of course, such an approach wouldn't necessarily tell us what we want to know about a simply-typed (partial) language. 

p8.  Isomorphisms are really partial isomorphisms here; so, any two types are "isomorphic" simply by giving to and from functions that always fail.  Please clarify.

p9.  I wasn't sure why "replace-lens" is limited to the identity isomorphism.  Can't we lift any partial isomorphism to a lens, or is there something special about the identity?

p9-10.  The align combinator seems a little ad hoc - it seems like the work done on the source by "source-condition" and "conceal" could be factored out to a separate, simpler combinator, the matching and creating to another combinator, and the proposed "align" defined by composing them.

p11. "matchs" - sp.

p15. In CaseVBranch, isn't the type (morally) equivalent to Lens S V?  It would be, if Iso was full isomorphisms rather than partial ones.  Does the difference matter here?

p16.  The first paragraph on this page argues that the approach in this paper is "putback-based" even though the lens framework used is the Foster et al.-style "pair of get and set" flavor.  I still do not understand how the putback-based approach differs formally from that style, and this paragraph convinces me further that there is no formal difference, since the same argument applies to show that Foster et al.'s approach is also "putback-based".  

That being the case, it seems like the distinction is in how one approaches defining the transformations and what combinators are considered natural and useful.  I still have to say that I don't find the putback-style combinators particularly intuitive or clear.  Is there an easy-to-characterize objective difference between "get-style" combinators and "putback-style" combinators, e.g. in terms of expressiveness or some other behavioral property?  

(I realize that Foster et al.'s approach is different enough, being based on trees rather than datatypes, that a formal comparison wouldn't be easy).

p18.  The following relevant paper seems like it should be mentioned as related work:

   Helmut Grohne, Andres Löh and Janis Voigtländer. Formalizing Semantic Bidirectionalization with Dependent Types, BX 2014


----------------------- REVIEW 2 ---------------------
PAPER: 46
TITLE: BiGUL: A Formally Verified Core Language for Putback-Based Bidirectional Programming
AUTHORS: Hsiang-Shang Ko, Tao Zan and Zhenjiang Hu

OVERALL EVALUATION: -1 (weak reject)
REVIEWER'S CONFIDENCE: 4 (high)

----------- REVIEW -----------
Summary: BiGUL is a new language for specifying putback-based
bidirectional transformations that has been formally verified using
Agda. The language builds on a previous putback-based language defined
by Pacheco et al. The main contributions of this paper include more
elegant and orthogonal definitions and the verified artifact.

Evaluation: The paper makes a solid contribution to the growing
literature on verified systems and is well-written and generally an
enjoyable read. However, the new contributions are hard to determine
since the putback-based approach and most of the constructs in this
core language have been extensively explored in previous bx
papers. Also, except for some discussions of how partiality is
encoded, the proofs for sequence, and the disucssion of source update,
the Agda formalization is not described in much detail.

Following are some comments and questions about the paper.

It is unclear from this paper if the main theorem on page 4 is a new
result or if it has been previously established in other papers on
putback-based bidirectional programming. Also, although the result
seems to be elementary, the paper does not give a proof.

A natural way to evaluate a language design is to show that it can
elegantly encode many examples. Unfortunately the paper only contains
a few examples, and most of them are quite small. Figure 2 is the only
larger example, and it is still just a snippet of a larger
application.

The early parts of the paper discuss replacing the dynamic checks with
statically verified primitives. However, the discussion of the
alignment primitives mentions "a few checks ... need to be inserted"
so it's unclear whether the primitives are guaranteed to be correct or
may sometimes be partial due to failures of run-time checks. A related
question: how do these primitives relate to Barbosa et al.'s matching
lenses? The paper is cited but not discussed in much detail.

The contributions in the section on source update (3.3) seems neat,
but the section is not well motivated. An example would help clarify
the need for this material.


----------------------- REVIEW 3 ---------------------
PAPER: 46
TITLE: BiGUL: A Formally Verified Core Language for Putback-Based Bidirectional Programming
AUTHORS: Hsiang-Shang Ko, Tao Zan and Zhenjiang Hu

OVERALL EVALUATION: 2 (accept)
REVIEWER'S CONFIDENCE: 3 (medium)

----------- REVIEW -----------
===== Paper summary =====

The paper presents a formally verified core language, called BiGUL,
for puback-based bidrectional programming. BiGUL is defined in Agda as
an embedded DSL (Domain Specific Language) and thus can be verified
using Agda. Indeed the authors formally prove that every BiGUL program
satisfies the well-behavedness properties.

===== Comments for author =====

* Points in favor

- It is the first formally verified bidirectional language.
- The way BiGUL is embedded in Agada is good.

* Points against

- There is not enough novelty.

* Evaluation

The presented work is reasonable. Designing and formally verifying a
bidirectional language for the first time is meaningful and
non-trivial work. Also, the way BiGUL is defined in Agda is good.  I
particularly like the idea of using the universe set and the pattern
set. Also, the details of the language design is well presented.

However, the key ideas do not seem to be very novel.  The idea of
shallow embedding and verification is well known. There might be some
novelty in the language design, compared to existing languages such as
Putlenses. However, at least it is not clearly stated in the paper.

* Typos

page 11: 
  list : U -> U -> U   
~> list : U -> U
