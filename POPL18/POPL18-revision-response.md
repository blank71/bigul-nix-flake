> POPL '18 Paper #2 Reviews and Comments
> ===========================================================================
> Paper #3 An Axiomatic Basis for Bidirectional Programming
>
>
> Review #3A
> ===========================================================================
> * Updated: 17 Sep 2017 4:54:49pm EDT
>
> Overall merit
> -------------
> 3. Weak reject - will not argue against
>
> Reviewer expertise
> ------------------
> X. Expert
>
> Paper summary
> -------------
> Summary
>
> [...]
>
> Strengths/weaknesses
>
> [...]
>
> Evaluation
>
> [...]
>
> High-level comments
>
> [...]
>
> The paper is also silent on the issue of symmetric transformations -
> in that case, both directions are like "put" in that both take the old
> version of X and new version of the Y and create the corresponding new
> version of X.  So a put-based approach where we need to verify that
> the put function satisfies the laws seems unlikely to save us any
> effort: we'd have to write both put functions, and then (somehow)
> prove that they are consistent with each other - perhaps by viewing
> the symmetric transformation as a span of asymmetric ones and
> verifying each lens in the span separately (using a common range
> predicate).

Addressed in the rebuttal. And symmetric lenses are now mentioned below Lemma
2.3 (L189).

> Comments for author
> -------------------
> Detailed comments
>
> 216: What is b?  I guess this stands for one of the (typed)
> expressions in figure 1.  But without seeing the semantics it is
> impossible to view this theorem as anything stronger than a definition
> of the (intended) semantics of b's.

Addressed in the rebuttal.

> 243: "freely use whatever relations" - so is the "host language" (cf
> 318) interpreted the same way (i.e. free use of whatever mathematical
> functions)?

Addressed in the rebuttal.

> 253: I guess the |-> notation used in rearrV, normal, and adaptive is
> by convention rendered as a "newline/indent" in examples?  This seems
> fine, but please explain the convention when it is introduced

Revised the text (L423–425) to

  The symbol `|->' indicates that b is syntactically a sub-node of
  `rearrV vpat -> wpat'; in displayed code, b is typeset in an indented
  block below `rearrV vpat -> wpat'.

And also added a variant of this explanation to the caption of Figure 1
(L254–256).

> 318: "in the host language" - which one? how should one reason about the host
> language in this setting?

Addressed in the rebuttal.

> 528: "intersected with the negations of the main conditions of all the
> previous rules" - making the rule order-sensitive.  This
> side-condition / \hat{M} notation is not clear in the figure, please
> add a definition of \hat{M} or a note to the caption to make it easier
> to understand this notation when it is first used.

Amended the caption of Figures 2 (L313-315) with

  \hat{M} denotes the ``actual main condition'' of a branch: the main condition
  M of the branch intersected with the negations of the main conditions of all
  the previous branches. ``Actual exit conditions'' \hat{E} are analogous.

> 745: This theorem is not proved (at least not in the main body of the
> paper), nor it there enough information to judge what is being proved;
> we need to know at least how BiGUL programs can be interpreted as
> (get,put) functions.

Addressed in the rebuttal. However, to clarify, added below Definition 2.1
(L162–165):

  In this paper we will provide an axiomatic semantics as the only formal
  definition of BiGUL's semantics, and omit the definitions of put and get
  (except for a few simple cases in Section 4.1) and proofs that rely
  essentially on them (like the proof of Theorem 2.2 below).  All the
  definitions and proofs are included in the supplementary Agda formalisation
  for reference.

For a few simple cases in Section 4.1, the put definitions are now explicitly
given (`put fail s v = Nothing', `put replace s v = Just v', and
`put (skip f) s v = if f s == v then Just s else Nothing').

In the Agda formalisation accompanying the original submission there wasn’t a
clear mapping between definitions/theorems in the paper and in the code (for
which we apologise). This has been amended in the version submitted for artifact
evaluation, where the file Everything.agda now explains where in the code the
definitions/theorems in the paper can be found.

> 859: Is the inner "replace * replace" equivalent to "replace" at
> (N,N)?  Is there a reason it is expanded out?

We said that there was no particular reason in the rebuttal, but this choice
seems to make Example 5.6 slightly easier to present, so we’re keeping this
unchanged.

> 1006: the list alignment definition seems to rearrange the source
> list; I'm not sure if / why this is necessary, but seems fine (it just
> means that consistency requires the source and view lists to ahve the
> same keys in the same order).  Is it harder to prove
> the correctness of a variation of this lens such that consistency only
> requires the same keys appear on both sides, but allows them to be in
> different orders (as in the matching lenses paper, I think)?

Addressed in the rebuttal.

> 1137: "ultimate aim of expressing all lenses" - this is a worthy goal,
> but I'm not sure I understand how you would know whether it was
> achieved.  For example, does this mean "expressing all lenses that
> could be expressed directly in a Turing complete language / Haskell /
> ML"?  It already isn't clear that BiGUL is "more expressive" than one
> of the combinator-based/"get-oriented" lens libraries.  Proving
> e.g. that a given set of lenses/lens combinators are "macro
> expressible" [Felleisen's definition] using BiGUL would be more persuasive here.

Addressed in the rebuttal.

> 1196: discussion of composition.  This rule refers to "l o r" but does
> not define how it behaves.  Usually with lenses, the definition of
> the put function of the composition relies on both put and get
> functions of the composed lenses. Maybe this is why this rule seems complicated.

Yes. Amended the sentence (L1233–1234) to say:

  the retentive behaviour of lens composition is rather chaotic and hard to
  reason about, because its put direction is defined in terms of both the put
  and get directions of the components.

> 1246: "Bidirectional programming has been highly declarative" - again,
> I think this is inaccurate.  Please be clearer about the advantages
> and disadvantages of different approaches rather than attributing the
> disadvantages of one approach (bidirectionalization) to all others.

See below.

> 1250: [Stevens 2010] cited to support the claim that "declarative
> approaches are hardly enough", but this paper critiques the QVT
> approach in model transformation, not lens combinators.

Addressed in the rebuttal.

> 1252: [Cheney et al. 2015] is cited as an example of investigating
> "more well-behavedness laws", but the point of that paper is not to do
> this but to consider least change criteria that might be not be
> all-or-nothing but might have a quantitative flavor.

Addressed in the rebuttal.

> 1282: Cheney et al. paper is now published as a journal article.
>
> James Cheney, Jeremy Gibbons, James McKinna, Perdita Stevens: On
> principles of Least Change and Least Surprise for bidirectional
> transformations. Journal of Object Technology 16(1): 3:1-31 (2017)

Updated.

> Reaction to author response
> ---------------------------
> Thanks to the authors for their detailed response.  Perhaps my review came across as a bit harsh; I do want to say that I think there is nice material here (as I thought I said in the review).  I fully appreciate the challenge of completely formalizing this kind of system in a prover/proof assistant; my perhaps poor choice of words "Agda tool" was not intended to be disparaging, I thought it was intended in the paper that one could think of this both as a proof of correctness and prototype implementation, but realize that my choice of words gave the impression I did not understand this.

Thank you, too, for the also very detailed review, which we appreciate, and
also for reading our rebuttal carefully and raising the score.

> The authors defend their (in my opinion) mischaracterization of previous work by saying essentially "yes, what we say in the introduction is misleading/simplistic, but we refer to a more accurate, detailed discussion in a later section so that's OK".  Sorry, I don't think that's OK, the introduction should be revised to avoid giving a misleading impression from the beginning.

Agreed — see below.

> Yes, Foster et al. present combinators that mostly "look like" the get direction (as a feature, not a bug).  But no, the behavior of the put direction obtained by refining this to express the put direction is not "essentially arbitrary" - at least in the sense  that "the implementation is choosing the behavior without any programmer control", which as you acknowledge in your response is not the case.  (Or if instead you mean that "essentially any desired put behavior can be obtained", then why is that bad?)  The paper should not is characterize previous work in this way.

This is in line with what we wrote in our rebuttal, so we will revise following
that (in particular, lens combinators and bidirectionalisation are converging to
the same programming model, so the conflated summary is justified). Revised the
abstract (L9–11), introduction (L55–60), and conclusion (L1287–1290) to say that
bidirectional programming has been based on a declarative model, and while ways
to customise consistency restoration behaviour are provided, they are usually ad
hoc and/or awkward to use.

> The authors do not really engage with my suggestion that their work can be motivated better by focusing on the ways in which your approach offers new advantages rather than ascribing specious disadvantages to previous work.  This is unfortunate; however, I am willing to raise my score and not block acceptance, provided acceptance is conditional on the authors revising the paper to address my concerns.

We thought we addressed this in the rebuttal when replying to “It is also not
clear to me that it is helpful for the programmer to only be able to write the
put direction”, where we argued for the putback-based approach. We’ve extended
the Q&A starting with “The semantics of range triples [...]” in Section 8
(L1215–1230) to make this point clearer.

> Review #3B
> ===========================================================================
> * Updated: 21 Sep 2017 1:56:16pm EDT
>
> Overall merit
> -------------
> 5. Accept - will argue for
>
> Reviewer expertise
> ------------------
> X. Expert
>
> Paper summary
> -------------
> * Summary
>
> [...]
>
> * Evaluation
>
> [...]
>
> * Detailed comments
>
> [...]
>
> Comments for author
> -------------------
> --- Page 2 ---
>
> line 62. Why do you use a rectangle in this example? Why not simply use a pair of numbers?

Addressed in the rebuttal.

> --- Page 4 ---
>
> line 167, “As noted by Ko et al., Theorem 2.2 gives a stronger well-behavedness guarantee”. You could say how it is stronger.

Added “in Foster et al.’s PutGet, for example, a successful |put| computation
does not guarantee the success of the subsequent |get| computation” (L172–174).

> --- Page 7 ---
>
> Figure 2. The intuition behind these constructs could be strengthened by giving the
> corresponding get, maybe relating them to the combinators of Foster 2007. For
> instance, replace would be id, and skip (fun _ -> v) would be const v.

We think otherwise — our experience of programming in BiGUL suggests that the
programmer does not actually need to think about the get semantics, hence the
omission of the get semantics throughout the paper (except for replace).

> --- Page 9 ---
>
> line 396. “We” should be “we”.

We’re following the Chicago style here.

> line 406. Please say what is “const ()”. (I guess const is fun x y -> x.)

Added “where const is the K combinator: const x y = x” (L414).

> line 422. Can there be variables in wpat that are not in vpat? I think not, because otherwise there would be an arity issue for R (in fact you later state that they are the same). If this is correct, why not simply say that vpat and wpat have the same variables? Also, can a variable appear several times in vpat?

Addressed in the rebuttal. To clarify, added “The intention is to represent a
closed $\lambda$-expression \ vpat -> wpat to be applied to the view” (L423–425).


> --- Page 10 ---
>
> line 489. An example of source rearrangement would be most welcomed.

Added Example 4.3 (view equality checking) (L494–518).

> --- Page 11 ---
>
> line 530, “We denote this actual main condition by M”. This is very handwavy. A more formal definition would be welcomed.

The English definition before the above sentence is precise enough (although
somewhat clumsy), we think.

> --- Page 12 ---
>
> line 564: “reunning” → “rerunning”

Corrected.

> --- Page 13 ---
>
> line 629, ⟨_⟩ (w′,h′). It took me a long time to parse this (the always true unary relation applied to (w',h')) and understand it is because of the exit pattern. A short mention of this would be most useful.
>
> line 634. Same comment about application of a relation.

The syntax has been explained in Section 3, and we feel that recapping the
syntax here disrupts the flow.

> --- Page 16 ---
>
> line 759. This is where making the get of replace explicit would be useful.

Which we did in the paper.

> --- Page 23 ---
>
> line 1091. Is the formal proof that {ss (v::_) | kv v ∈ map ks ss} implies {ss (v::vs) | ⟨(s::_) (v::_) | ks s = kv v⟩ (extract ks kv v ss) (v::vs)} very complex?

Addressed in the rebuttal.

> --- Page 25 ---
>
> replaceAll example. Could it be possible to have a version of replaceAll where put [] v = [] ? It seems it's not possible, because get would then be defined on [] which is problematic.

Addressed in the rebuttal.

> --- Page 26 ---
>
> line 1227. Can you also prove that if ss = [] then length ss' = 1?

Addressed in the rebuttal.

> Reaction to author response
> ---------------------------
> The answers were not fully satisfactory, but i maintain my positive mark

Thanks!

>
> Review #3C
> ===========================================================================
>
> Overall merit
> -------------
> 4. Weak accept - will not argue for
>
> Reviewer expertise
> ------------------
> Z. Outsider
>
> Paper summary
> -------------
>
> [...]
>
> Some more detailed comments.
> - p. 3, 2nd paragraph: You talk about a "direction" here, but it is not clear what "direction" means in this context.

Bidirectional programs have two directions, get and put; this has been
established before this point.

> - p.2, "put uniquely determines get", p. 3, "...how they can characterise the get behavior to some extent" - this sounds a bit contradictory.

Addressed in the rebuttal.

> - p.4, after Theorem 2.2: It is unclear what you mean by "non-well-behavedness" here. If Theorem 2.2 gives the definition of well-behavedness, how can programs satisfying it not be well-behaved? Obviously you refer to something that exceeds Theorem 2.2, but it is not clear what. It is also unclear what the "various checks at runtime" are.

Changed one occurrence of “non-well-behavedness” to “possible violations of
well-behavedness” (L176).
