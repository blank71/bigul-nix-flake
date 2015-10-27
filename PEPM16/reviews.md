Dear Hsiang-Shang,

We are happy to inform you that your submission, BiGUL: A Formally Verified Core Language for Putback-Based Bidirectional Programming (number 6), has been 
selected for the PEPM 2016 Technical Program. The reviews for your submission are provided 
below. We hope that you will find this feedback useful to prepare the final version of your 
paper.

Best regards,
Martin Erwig and Tiark Rompf
PEPM 2016 Program Chairs


----------------------- REVIEW 1 ---------------------
PAPER: 6
TITLE: BiGUL: A Formally Verified Core Language for Putback-Based Bidirectional Programming
AUTHORS: Hsiang-Shang Ko, Tao Zan and Zhenjiang Hu

OVERALL EVALUATION: 1 (weak accept)
REVIEWER'S CONFIDENCE: 2 (low)

----------- REVIEW -----------
The paper presents a core language for bidirectional programming. Although every program directly embodies both directions of bidirectional programming, a program is written and read only like a putback transformation. The main contribution of this paper is that the language is defined in Agda and hence every program automatically comes with a proof that the two well-behavedness properties of bidirectional programming hold.

I am no expert on bidirectional programming, but I believe that this paper brings the subject a step forward. As the authors state in the conclusion, the next natural step is to fully use dependent types such that a bidirectional program guarantees that the two defined transformations exist and are total.

The presence of dynamic checks and the fact that both transformations are still defined as partial functions worries me. Each of the combinators of the BiGUL language could be defined such that both transformations return nothing and the proofs are trivial. I do not see how any programmer writing a program like in Figure 2 or Section 3.7 can have confidence that their program does not just return nothing. I would like to see at least a discussion of this problem.

It seems to me that the idea of reifying the monadic combinators and computation steps of the data type Par is a contribution of this paper that might be applied in different areas. Currently the idea and the discussion with the alternative in Section 2.2 is rather hidden. It would be good to make this more prominent in the paper and also in introduction and conclusion.

The majority of the paper is too technical for my liking. It feels like the technical documentation of the implementation. However, a scientific paper should be about reusable ideas, that readers might apply in different settings. I’d like to see less technical details and instead more focus on ideas.

Details:

Page 1: “and the other *as the* view”
Page 1: “BiGUL is specified only”: specified is the wrong word, as this paragraph is only about the syntax, not the semantics.
Page 1: “BiGUL is … as monadic program*s*” singular and plural conflict

I found the explanations of the two properties in the second half of Section 2 a bit confusing. Some descriptions are repeated with variation; a single description for each would be better.

The second part of Section 2.2 considers an alternative design. I think the authors should check the English grammar of the First or Second Conditional.

Page 3: “a probably easiest way” the?

The last paragraph before 3.2.1 raises a problem which is solved in 3.2.1. I do not think that separating problem and solution in this way is good, but a solution should immediately follow a problem (maybe both in a sub subsection).

Even in the conclusion the last but one paragraph raises a problem which the last paragraph answers. I find this structure irritating, because at first I think that a question is raised without an answer (the paragraph ends), but then suddenly an answer is given.

Having Figures 2 and 3 far away from the referring text does make reading difficult.


----------------------- REVIEW 2 ---------------------
PAPER: 6
TITLE: BiGUL: A Formally Verified Core Language for Putback-Based Bidirectional Programming
AUTHORS: Hsiang-Shang Ko, Tao Zan and Zhenjiang Hu

OVERALL EVALUATION: 2 (accept)
REVIEWER'S CONFIDENCE: 4 (high)

----------- REVIEW -----------
This paper presents BiGUL, a language for describing bidirectional transformations (BXs). No user-facing syntax for BiGUL is given, but its dependently-typed abstract syntax and its semantics are formalized in Agda. The formalization proves that BiGUL can only represent well-behaved BXs, that is, that all BXs satisfy the well-known GetPut and PutGet laws. The PutGet law guaranteed by BiGUL is stronger than the usual definition.

Overall, I liked this paper and recommend it for acceptance.

As a reader fluent in BXs and functional programming, I found the paper to be very readable despite a limited Agda background. The presentation of the semantic domain and proof infrastructure in Section 2 was especially well done, making a rather sophisticated encoding clear and understandable.

The paper builds on the authors' previous work on putback lenses (one of these papers was at PEPM 2014). The major new contribution is the Agda formalism, which is valuable and interesting. The paper does a very good job of clarifying its position relative to previous and related work on BXs. In Section 4, this positioning seems a bit defensive, but I did appreciate the directness and clarity.

One thing I would strongly recommend is moving Section 3.5 up to before Section 3.2. I think I see the motivation for putting this late in Section 3 (it is rather long and involved relative to the other constructs), but understanding how pattern matching works is essential to understanding the two case-analysis constructs in Sections 3.2 and 3.3. The presentation in Section 3.5 is very good, but I was lost in Sections 3.2 and 3.3 until skipping ahead and reading this. Moving this up will also help clarify the example in Figure 2 more quickly.

Additionally, simple examples in Section 3.2 and 3.4 would be helpful. The comparison-with-zero example in Section 3.3 was very helpful to understand the role and intention of case-analysis on views. Similarly tiny examples for the other constructs would be great.

The monad reification trick should include a citation and brief discussion in related work, since it is not new to this paper. Unfortunately, I don't have a good recommendation for this. If it has no unique source, then I still think it would be useful to point out other applications of the same trick.


----------------------- REVIEW 3 ---------------------
PAPER: 6
TITLE: BiGUL: A Formally Verified Core Language for Putback-Based Bidirectional Programming
AUTHORS: Hsiang-Shang Ko, Tao Zan and Zhenjiang Hu

OVERALL EVALUATION: 1 (weak accept)
REVIEWER'S CONFIDENCE: 3 (medium)

----------- REVIEW -----------
Summary

This paper proposes a new core language for bidirectional transformation
based on the 'putback'-based model.  The distinguished feature of 
this language is that all primitives of the language are formally 
defined, and formally guaranteed to satisfy two desirable properties 
about well-behavedness. The paper explains the primitives in a great 
detail, using the dependently typed language Agda, which is also served
as the proof language for the properties. It also gives a few 
programming examples which are simple, but non trivial.

Assessment

This paper is well motivated, addresses an important issue in the area,
and presents a solid result.  The addressed problem is how to design
a language which is statically guaranteed to satisfy the well-behavedness
properties, and the authors have given a formal proof for it, using Agda.  
The paper reveals that this development is not trivial, as rather 
intricate and complex treatment is needed for several primitives, and 
the paper shows a concrete solution for the difficult cases.  
The formalization of the semantics in Agda is well explained, and the 
proof of the properties are mentioned briefly.  All these are interesting, 
and I think the paper is valuable, and should be published.

As formal verification work, readers wants to know what are difficulties
and which tricks are used to overcome the difficulties.
Section 2 of the present paper presents such an aspect of its formalization.
It argues that the straightforward representation via monadic combinators 
are not suitable for this work, and introduces a slightly different 
formalization, which is I found interesting.

A negative side of this paper is that the paper does not really 
compare the proposed language with other, existing languages in its
expressive power, performance, or any other scientific measures.
It is unsatisfactory since the paper is proposing a new language
BiGUL, and the authors argue that it should serve as a core language
of bidirectional transformations. From the (very detailed) description 
of the language primitives, one can expect that BiGUL can express a 
large class of examples for bidirectional transformations, but since 
its semantics is defined in terms of Agda, which has relatively 
complicated types, it is not completely clear if BiGUL can express 
all (or most) useful examples that are expressible in (for instance) Biflux.   

The authors claim (in Conclusion) that "the expressive power of the
current BiGUL is not obviously stronger than existing lenses", which 
is hard to understand as a scientific argument.
Readers want to know (at least) if BiGUL is as expressive as existing lenses 
(or other formulations) or not, which should be mentioned in the paper.

Another concern of mine is that, if BiGUL is well designed as the target 
of theoretical study, namely, if it is sufficiently 'small' as a core
language. Since several primitives in BiGUL do complicated jobs, this reviewer
wonders if BiGUL can be expressed by a simpler set of primitives.  
I believe simplicity is very important as the authors plans to extend the 
language to cover, for instance, general recursion.  The present paper does 
not argue much about their design decisions of the core language.

Conclusion

I think the formal development of the paper is valuable and worth
published, though the paper has some weakness as a proposal of a
new programming language.  Thus I recommend (weak) accept.

Other comments

The paper tries to explain each primitive by plain texts and the 
formalization in Agda, and I found the text explanations are 
occasionally hard to follow.  For instance, Sect. 3.4 includes a 
paragraph with 24 lines which explains the put semantics of align.  
I recommend the authors to insert a simple, concrete example and
explains its behavior, rather than the general case.


----------------------- REVIEW 4 ---------------------
PAPER: 6
TITLE: BiGUL: A Formally Verified Core Language for Putback-Based Bidirectional Programming
AUTHORS: Hsiang-Shang Ko, Tao Zan and Zhenjiang Hu

OVERALL EVALUATION: 2 (accept)
REVIEWER'S CONFIDENCE: 3 (medium)

----------- REVIEW -----------
It was shown in previous work that the 'get' direction of a bidirectional lens, if exists, is uniquely determined by the 'put' direction. The discovery suggests a new approach to bidirectional programming -- to specify 'put', and have 'get' automatically constructed. The 'put' direction, however, is often much more complex. It is thus a challenge to design a language that is expressive enough while, to some extent, guarantee or at least increase the likelihood that the specified 'put' does induce a 'get'.

This paper presents a language BiGUL. The language is defined in a novelly formal manner: the semantics of the language is a monadic program. To make proofs about such programs easier, however, monadic programs are deeply embedded as a datatype, whose big-step semantics is reified as an Agda type. This technique, if not presented elsewhere, is a good contribution of this paper.

The language BiGUL consists of only 8 operations. Some of the operators, in particular 'align' and 'rearr', however, are rather complex. Indeed one needs some formal proof to be sure that the constructed program is correct.

Overall, I think this is an interesting paper worth publishing.

Minor Comments
--------------
p5. Figure 2, line 5. 
'update' should be indented more to make it clear that it is an argument to 'rearr'.

p5. Figure 3, "get = get" and "put = put-with-adaption..."
"get = get" does not look right, since we want something of type S -> Par V, while the 'get' defined below has type "List .. -> S -> Par V". 'put' does not look type correct either.