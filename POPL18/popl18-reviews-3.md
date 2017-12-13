POPL '18 Paper #3 Reviews and Comments
===========================================================================
Paper #3 An Axiomatic Basis for Bidirectional Programming


Review #3A
===========================================================================
* Updated: 17 Sep 2017 4:54:49pm EDT

Overall merit
-------------
3. Weak reject - will not argue against

Reviewer expertise
------------------
X. Expert

Paper summary
-------------
Summary

This paper proposes a Floyd-Hoare-style logic for reasoning about
bidirectional transformations, e.g. asymmetric lenses.  It focuses on
verifying properties of the "put" direction using "put triples" {P} b
{Q} where b is an expression in a core language representing BiGUL, a
bidirectional language with Haskell DSL and standalone
implementations.  BiGUL contrasts with previous work on lens
combinators/bidirectional languages chiefly in that programs (are
intended to) correspond to programmers' intuitions regarding how to
implement the "put" direction, rather than resembling the "get"
direction. This appears to open up the language somewhat in terms of
expressiveness compared to lens combinators, while also making it
possible to write programs that do not denote a well-behaved lens.
The program logic in this paper intends to fill this gap, by providing
rules (implemented in an Agda tool) that can be used to verify
well-behavedness.  It also turns out to be necessary to verify "range
triples", which (in my view) actually amount to verifying properties
of the "get" direction.

The paper gives a number of examples of reasoning using these systems
(including) and concludes with a discussion of natural questions
regarding the expressiveness and relationship to other formalisms.

Strengths/weaknesses

+ Presents a program logic suitable for proving correctness of bidirectional transformations written in an expressive language
- Details of semantics/proof of key properties not clear enough in the paper
- Argumentative and (in my view unnecessarily) mischaracterizes some prior work as having the disadvantages of other approaches
- The need for both "put triples" to reason about put and "range triples" (apparently) to reason about get undercuts the authors' argument that focusing only on the put direction is beneficial

Evaluation

I have mixed feelings about this paper.  On the one hand, at a technical
level the idea of a Hoare-style logic for verifying properties of
bidirectional programs (in the context of a language with primitives
that seem well-tailored to writing lenses / bidirectional programs more
directly) is intriguing.  I would be more excited about the paper if it was
focused on exploring this (perhaps for "classic" get/put lenses written
using BiGUL) rather than advocating for a put-oriented/put-only approach.

On the other hand, the authors' apparent insistence on
mischaracterizing all work on "lenses/combinators" as having the same
disadvantages as some approaches to "bidirectionalization" (see below)
strikes me as inappropriate for a scientific paper.  (this is not the
first paper I've reviewed that has made this argument, and it has not
gotten more persuasive).

As discussed further below, I actually don't think this argument is
necessary to justify what the authors are doing either.  Just as any
type system rules out useful programs that are type-correct at run time, it
is plausible that any fixed set of (typed, total) lens combinators
might rule out lenses that are semantically valid/useful, so one can
justify the search for more expressive languages and verification
techniques that can be used to check correctness without presenting
previous work inaccurately.

High-level comments

55-58: "what Foster et al. [2007]’s lenses and all subsequent
get-based approaches offer is essentially a highly declarative
programming model, in which the programmer only specifies a
consistency relation (in terms of a get transformation) and obtains a
consistency restorer (a put transformation) that is guaranteed (by
well-behavedness) to respect the consistency relation but is otherwise
arbitrary"

This is a somewhat tendentious claim; it conflates two or three
different approaches to bidirectional transformations and (in my view
falsely) attributes the limitations of some of them (e.g. declarative
approaches, bidirectionalization) to others (e.g. lenses).
Specifically:

- the "relational" approach, dating to Meertens [1998] and formalized
  by Stevens [2007 etc.] in which one specifies a consistency relation
  first and then looks for functions that restore consistency between
  two models.  (But even then, usually the bidirectional
  transformation consists of a consistency relation plus functions
  that restore consistency on one side or the other.)

- the "bidirectionalization" approach, in which one writes the get
  function in some (perhaps constrained) functional language, and then
  does some program transformation to construct a put function that
  satisfies the laws.

- the "lens combinator" approach, in which bidirectional programs are
  built up from constants and combinators that are equipped with both
  get and put functions, which are proved (in advance) to satisfy or
  preserve the laws, so that the end result of a composition of the
  operations also does.

There is some sense to describing the Foster et al. style lens
approach as "the programmer only specifies the consistency relation
(in terms of a get transformation) and obtains a consistency restorer"
but in the lens approach there can be several variants of
lenses/combinators that have different put behavior, so it would be
more accurate to say that the Foster-style lenses, provide a language
of operations in which programmers need to think about both directions
at once to program successfully, and (IMO) inaccurate to claim that
the put directions are "otherwise arbitrary".

I do think it is reasonable to pursue alternative approaches to
bidirectional programming that provide increased expressiveness or
control to programmers in both directions, rather than thinking of the
get direction as primary and the put direction as an afterthought (as
in e.g. bidirectionalization); I just do not agree that this is a fair
characterization of Foster et al.'s approach.

It is also not clear to me that it is helpful for the programmer to
only be able to write the put direction; it seems that this makes it
more difficult to be confident that the get direction is doing what is
expected - perhaps I have written what seems like a sensible put
function but it implements a different get function than I want.  What
if I want to verify that the get direction has a certain property?  If
it is invisible that seems hard.  But in fact, theorem 5.2 seems to
indicate that the "range triples" are really just Hoare triples for
reasoning about the get direction, which seems to undermine the claim
that this is a "put-oriented" system - "get" still even appears in
lemma 5.3 (though I guess in principle it could be removed.)

The paper is also silent on the issue of symmetric transformations -
in that case, both directions are like "put" in that both take the old
version of X and new version of the Y and create the corresponding new
version of X.  So a put-based approach where we need to verify that
the put function satisfies the laws seems unlikely to save us any
effort: we'd have to write both put functions, and then (somehow)
prove that they are consistent with each other - perhaps by viewing
the symmetric transformation as a span of asymmetric ones and
verifying each lens in the span separately (using a common range
predicate).

Comments for author
-------------------
Detailed comments

216: What is b?  I guess this stands for one of the (typed)
expressions in figure 1.  But without seeing the semantics it is
impossible to view this theorem as anything stronger than a definition
of the (intended) semantics of b's.

243: "freely use whatever relations" - so is the "host language" (cf
318) interpreted the same way (i.e. free use of whatever mathematical
functions)?

253: I guess the |-> notation used in rearrV, normal, and adaptive is
by convention rendered as a "newline/indent" in examples?  This seems
fine, but please explain the convention when it is introduced


318: "in the host language" - which one? how should one reason about the host
language in this setting?

528: "intersected with the negations of the main conditions of all the
previous rules" - making the rule order-sensitive.  This
side-condition / \hat{M} notation is not clear in the figure, please
add a definition of \hat{M} or a note to the caption to make it easier
to understand this notation when it is first used.

745: This theorem is not proved (at least not in the main body of the
paper), nor it there enough information to judge what is being proved;
we need to know at least how BiGUL programs can be interpreted as
(get,put) functions.

859: Is the inner "replace * replace" equivalent to "replace" at
(N,N)?  Is there a reason it is expanded out?

1006: the list alignment definition seems to rearrange the source
list; I'm not sure if / why this is necessary, but seems fine (it just
means that consistency requires the source and view lists to ahve the
same keys in the same order).  Is it harder to prove
the correctness of a variation of this lens such that consistency only
requires the same keys appear on both sides, but allows them to be in
different orders (as in the matching lenses paper, I think)?

1137: "ultimate aim of expressing all lenses" - this is a worthy goal,
but I'm not sure I understand how you would know whether it was
achieved.  For example, does this mean "expressing all lenses that
could be expressed directly in a Turing complete language / Haskell /
ML"?  It already isn't clear that BiGUL is "more expressive" than one
of the combinator-based/"get-oriented" lens libraries.  Proving
e.g. that a given set of lenses/lens combinators are "macro
expressible" [Felleisen's definition] using BiGUL would be more persuasive here.

1196: discussion of composition.  This rule refers to "l o r" but does
not define how it behaves.  Usually with lenses, the definition of
the put function of the composition relies on both put and get
functions of the composed lenses. Maybe this is why this rule seems complicated.

1246: "Bidirectional programming has been highly declarative" - again,
I think this is inaccurate.  Please be clearer about the advantages
and disadvantages of different approaches rather than attributing the
disadvantages of one approach (bidirectionalization) to all others.

1250: [Stevens 2010] cited to support the claim that "declarative
approaches are hardly enough", but this paper critiques the QVT
approach in model transformation, not lens combinators.

1252: [Cheney et al. 2015] is cited as an example of investigating
"more well-behavedness laws", but the point of that paper is not to do
this but to consider least change criteria that might be not be
all-or-nothing but might have a quantitative flavor.

1282: Cheney et al. paper is now published as a journal article.

James Cheney, Jeremy Gibbons, James McKinna, Perdita Stevens: On
principles of Least Change and Least Surprise for bidirectional
transformations. Journal of Object Technology 16(1): 3:1-31 (2017)

Reaction to author response
---------------------------
Thanks to the authors for their detailed response.  Perhaps my review came across as a bit harsh; I do want to say that I think there is nice material here (as I thought I said in the review).  I fully appreciate the challenge of completely formalizing this kind of system in a prover/proof assistant; my perhaps poor choice of words "Agda tool" was not intended to be disparaging, I thought it was intended in the paper that one could think of this both as a proof of correctness and prototype implementation, but realize that my choice of words gave the impression I did not understand this.

The authors defend their (in my opinion) mischaracterization of previous work by saying essentially "yes, what we say in the introduction is misleading/simplistic, but we refer to a more accurate, detailed discussion in a later section so that's OK".  Sorry, I don't think that's OK, the introduction should be revised to avoid giving a misleading impression from the beginning.

Yes, Foster et al. present combinators that mostly "look like" the get direction (as a feature, not a bug).  But no, the behavior of the put direction obtained by refining this to express the put direction is not "essentially arbitrary" - at least in the sense  that "the implementation is choosing the behavior without any programmer control", which as you acknowledge in your response is not the case.  (Or if instead you mean that "essentially any desired put behavior can be obtained", then why is that bad?)  The paper should not is characterize previous work in this way.

The authors do not really engage with my suggestion that their work can be motivated better by focusing on the ways in which your approach offers new advantages rather than ascribing specious disadvantages to previous work.  This is unfortunate; however, I am willing to raise my score and not block acceptance, provided acceptance is conditional on the authors revising the paper to address my concerns.



Review #3B
===========================================================================
* Updated: 21 Sep 2017 1:56:16pm EDT

Overall merit
-------------
5. Accept - will argue for

Reviewer expertise
------------------
X. Expert

Paper summary
-------------
* Summary

This paper presents a Hoare-style logic for the bidirectional language BiGUL. BiGUL is a putback-based language, in the sense that the programmer only writes one program for the put direction, and the other (get) direction is automatically derived. By construction, BiGUL programs are well behaved, in the sense that both directions are consistent. More precisely, assuming a set of sources and a set of views, the get direction is a partial function from sources to views, and the put direction is a partial functions from views and sources to sources. If putting v in s is defined and results in s', then get s' is defined and is v. Conversely, if get s is defined and is v, then putting v in s is defined and is s.

The Hoare-style logic presented enables explicit statements of the consistency between sources and views for a given program. In addition, another set of inference rules are defined to (under) approximate the range of the put direction. As a get is always defined on sources that are the result of a put, this implies that the range triples approximate where the get direction is defined. Both logics are put to contribution to prove total forward consistency: if a program satisfies some consistency constraints and is shown to have some range, then for any s in that range get is defined and the resulting view is consistent with s.

The paper presents a complex example of a bidirectional operator on lists that aligns them according to some keys. Both the consistency and range are given for the program. Finally, the BiGUL approach is compared to other bidirectional programming approaches.

* Evaluation
** Strength
- The paper is very well written, and most examples and rules descriptions are easy to follow.
- The design of the language and of the logics are well motivated.
- The language is small, yet it is able to tackle complex examples.
- Many examples are presented.
- The treatment of recursion is pragmatic, yet clearly formalized.

** Weaknesses
- It's difficult to evaluate the correctness of the logic without having a semantic. In addition, one can easily infer the semantics in the putback direction, but it's much more difficult to guess it in the get direction if one is not used to bidirectional languages.
- Some definitions are very informal and proofs are missing. As there is an Agda formalization, this is a minor weakness.

* Detailed comments
I have found the paper very pleasant to read, as it's clear, technically sound, with many examples. Section 4.5 in particular was quite impressive, as it succeeds in explaining a very complex rule. I also found the discussion in Section 8 quite helpful, as it answered some questions I had while reading the paper. I would have liked more intuition about the semantics, especially in the get direction, but I don't know what should be removed to make space for that.

Comments for author
-------------------
--- Page 2 ---

line 62. Why do you use a rectangle in this example? Why not simply use a pair of numbers?


--- Page 4 ---

line 167, “As noted by Ko et al., Theorem 2.2 gives a stronger well-behavedness guarantee”. You could say how it is stronger.


--- Page 7 ---

Figure 2. The intuition behind these constructs could be strengthened by giving the
corresponding get, maybe relating them to the combinators of Foster 2007. For
instance, replace would be id, and skip (fun _ -> v) would be const v.


--- Page 9 ---

line 396. “We” should be “we”.

line 406. Please say what is “const ()”. (I guess const is fun x y -> x.)

line 422. Can there be variables in wpat that are not in vpat? I think not, because otherwise there would be an arity issue for R (in fact you later state that they are the same). If this is correct, why not simply say that vpat and wpat have the same variables? Also, can a variable appear several times in vpat?


--- Page 10 ---

line 489. An example of source rearrangement would be most welcomed.


--- Page 11 ---

line 530, “We denote this actual main condition by M”. This is very handwavy. A more formal definition would be welcomed.


--- Page 12 ---

line 564: “reunning” → “rerunning”


--- Page 13 ---

line 629, ⟨_⟩ (w′,h′). It took me a long time to parse this (the always true unary relation applied to (w',h')) and understand it is because of the exit pattern. A short mention of this would be most useful.

line 634. Same comment about application of a relation.


--- Page 16 ---

line 759. This is where making the get of replace explicit would be useful.


--- Page 23 ---

line 1091. Is the formal proof that {ss (v::_) | kv v ∈ map ks ss} implies {ss (v::vs) | ⟨(s::_) (v::_) | ks s = kv v⟩ (extract ks kv v ss) (v::vs)} very complex?


--- Page 25 ---

replaceAll example. Could it be possible to have a version of replaceAll where put [] v = [] ? It seems it's not possible, because get would then be defined on [] which is problematic.


--- Page 26 ---

line 1227. Can you also prove that if ss = [] then length ss' = 1?

Reaction to author response
---------------------------
The answers were not fully satisfactory, but i maintain my positive mark



Review #3C
===========================================================================

Overall merit
-------------
4. Weak accept - will not argue for

Reviewer expertise
------------------
Z. Outsider

Paper summary
-------------
This paper proposes a domain-specific language for specifying bidirectional transformations in the style of lenses. The main novelty of the language is a kind of Hoare logic to reason about such transformations. The language is presented by means of typing rules and an axiomatic semantics. The design is validated by means of a case study on key-based list alignment.

This looks like a nice and solid contribution. The presentation is thorough and well-validated. This reviewer is not an expert on lenses and Hoare-style logics, so my main comments are about presentation.

First of all, I think the paper needs a better motivation. What exactly is the problem the paper tries to solve? Why is it hard to reason about bidirectional programming without such an axiomatic semantics (e.g. why is ordinary algebraic reasoning not sufficient)?

Secondly, I think the paper suffers from a lack of an informal, example-driven overview. I believe the proposal to write a paper by first giving a complete informal, example-guided overview of the approach before coming to the formal part stems from Simon Peyton Jones. In any case, I think this paper would also benefit greatly from such an overview. This reviewer got lost in the details around section 4.4 and 4.5. Useful examples to explain rearrV, rearrS, case etc. would have been quite helpful. The small examples that are presented there (e.g. keepHeight in 4.4) were not sufficient to give a lot of intuition, especially since good explanations (like a reading of the example in plain English) are missing.

I was also missing some intuition or explanation of the expressiveness of the DSL.

Some more detailed comments.
- p. 3, 2nd paragraph: You talk about a "direction" here, but it is not clear what "direction" means in this context.
- p.2, "put uniquely determines get", p. 3, "...how they can characterise the get behavior to some extent" - this sounds a bit contradictory.
- p.4, after Theorem 2.2: It is unclear what you mean by "non-well-behavedness" here. If Theorem 2.2 gives the definition of well-behavedness, how can programs satisfying it not be well-behaved? Obviously you refer to something that exceeds Theorem 2.2, but it is not clear what. It is also unclear what the "various checks at runtime" are.



Response1 Response by Hsiang-Shang Ko <hsiang-shang@nii.ac.jp>
===========================================================================
We thank the reviewers for their effort. To keep the response short, we’ll focus on addressing Reviewer A’s concerns.

In the paper there are answers to most, if not all, of Reviewer A’s questions, especially in Section 8. We ask Reviewer A to take these parts of the paper into consideration.

**“making it possible to write programs that do not denote a well-behaved lens”:** No, BiGUL programs are always well-behaved (Theorem 2.2).

**“providing rules (implemented in an Agda tool)”:** Curious expression. We’d say that the rules are formalised and proved correct using the Agda proof assistant.

**55–58:** This is why we put “See Section 8 for further discussion” after the sentence Reviewer A quoted — the second and third Q&As in Section 8 (1145–1175) answer Reviewer A’s questions, in particular clarifying at length that the get-based approaches do offer some control of put behaviour but the programmer ends up having to reason in both directions, just as Reviewer A says. Regarding the three approaches mentioned by Reviewer A, the "relational" approach is more like a conceptual framework (in which, e.g., asymmetric lenses can be discussed), and the bidirectionalisation and combinator approaches have been converging to the same programming model, as mentioned in the third Q&A. And this model is in effect declarative in our opinion: As explained in the second Q&A, the design of Foster et al.’s combinators deliberately makes them look like get programs. Instead of programming the combinators in both directions at once, which is impossible, the more sensible way is to write a get program and then annotate it with put details (which can involve switching to different versions of combinators with the same get behaviour). We don’t think this development process is too different from tuning a declarative program (for performance, nuanced behaviour, etc). We could back off a bit and replace “but otherwise arbitrary” with something milder, but in any case the perspective presented in Section 8 is accurate.

**“It is also not clear to me that it is helpful for the programmer to only be able to write the put direction”:** The whole point of the logic is that, if we prove a strong enough put triple (e.g., one whose precondition is always true), even without a range triple we can already know the get behaviour is constrained by the consistency relation, so it’s impossible to end up “implement[ing] a different get function”. This is explained by the paragraphs below Theorems 3.8 and 5.4, and also emphasised multiple times in Sections 8 and 9.

**“theorem 5.2 seems to indicate that the "range triples" are really just Hoare triples for reasoning about the get direction, which seems to undermine the claim that this is a "put-oriented" system”:** Again, this is explicitly addressed by the fourth Q&A in Section 8 (1184–1192).

**“The paper is also silent on the issue of symmetric transformations”:** Symmetric lenses are a fairly different model from asymmetric lenses (as they don’t have nice properties like Lemma 2.3), and there’s much less work on those, especially when it comes to practical programming. Within the space restriction we can only discuss the most relevant work. We could mention symmetric (and edit-based) frameworks if we have more space.

**216:** The theorem statement begins with “Let b : S <- V”, saying that b is a BiGUL program (Definition 2.1). And you’re right — presentation-wise, this theorem is intended more as a definition. Content-wise it is formally verified.

**318:** “Agda imperfectly disguised as Haskell” (132–141).

**745:** “Everything in this paper from theorems to derivation examples has been formalised and checked in Agda [...] provided as supplementary material” (132).


Detailed responses (exceeding the word limit)
=============================================

The whole Agda formalisation was provided as supplementary material, and is also available in HTML for easy reference at:

>  https://josh-hs-ko.github.io/Agda/BiGUL-Logic/Everything.html

Review A
--------

**859:** Yes. And there’s no particular reason actually. (We discovered this only after submitting.)

**1006:** We’ve been able to write things that do sorting in the get direction, which is indeed more difficult (and, in particular, requires lens composition, which we hesitate to deal with now).

**1137:** In a sense BiGUL is already “BX-complete” because of the existence of the emb program (Example 4.4), but that’s obviously not a good enough completeness to have — so, thanks for the nice suggestion about Felleisen’s macro expressivity. (We’re not claiming that we have achieved the goal though.)

**1250:** We are saying that, for bidirectional applications in general (which are not necessarily developed using lenses), declarative approaches are not enough.

**1252:** We’re using a general sense of “well-behavedness” here, describing the kinds of (quantitative) laws in that paper as some forms of behavioural requirements that we might want the bidirectional applications to have, like we want correctness (wrt a consistency relation) and hippocraticness. (If this explanation is not good enough we can cite Diskin’s lax PutPut paper in BX’17 instead.)


Review B
--------

**62:** It provides a visual intuition for the example (which is helpful when talking about, e.g., keeping the height-to-width ratio), but otherwise unimportant.

**422:** Yes, vpat and wpat should have the same variables. And vpat (in a program) should not have duplicated variables (but we need to allow that in the comprehension relation syntax).

**1091:** No, it’s only 12 lines of code (https://josh-hs-ko.github.io/Agda/BiGUL-Logic/HoareLogic.Examples.Alignment.html#4102) expressing a straightforward case analysis. (The Agda code uses facilities in the Agda standard library rather than the more Haskell condition ‘kv v `elem` map ks ss’ though.)

**p25 replaceAll example:** Not possible, you’re right.

**1227:** Yes, we’ve just tried — it takes only two lines of change (one on the spec and the other the proof).


Review C
--------

**“What exactly is the problem the paper tries to solve?”:** The problem is probably somewhat common to (embedded) DSLs — we usually have to expand the definitions and reason in the host language, rather than staying at the DSLs’ abstraction levels. The situation is particularly messy for lens combinators since they have fairly complicated semantics. This point is briefly touched in Sections 8 & 9, and we can mention this in the introduction.

**“The small examples that are presented there (e.g. keepHeight in 4.4) were not sufficient to give a lot of intuition, especially since good explanations (like a reading of the example in plain English) are missing.”:** Doesn’t the paragraph directly below keepHeight explain the program?

**Detailed comments p2:** Because put triples are not enough; we still need range triples to know the domain of get.

**Detailed comments p4:** It’s about the implementation of the put and get interpreters. For example, ‘skip f’ checks at runtime that f s = v holds for the current source s and view v. It returns s iff that check succeeds.
