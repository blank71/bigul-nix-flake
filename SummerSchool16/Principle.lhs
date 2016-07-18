% !TEX root = paper.tex

%include lhs2TeX-macros.lhs

\section{Into BiGUL's Bidirectionality}

We have been writing |put| programs, usually having a corresponding |get| in mind but not explicitly describing it, and yet BiGUL is capable of finding the right |get| behaviour as if reading our mind. How? We will see that, when writing a BiGUL program, we are always simultaneously describing both a |put| function and a |get| function, which are guaranteed to be a well-behaved pair. And the ``mind-reading'' ability is far from magic: Well-behavedness directly implies that |get| is uniquely determined by |put|, which is the main motivation for designing a putback-based language. We will look at several constructs of BiGUL in detail to get a taste of such design.

\subsection{Lenses, well-behavedness, and the fundamental theorem}

Formally, we call a well-behaved pair of |put| and |get| a \emph{lens}:
\begin{definition}[lens]
A \emph{lens} between a source type~$s$ and a view type~$v$ consists of two functions:
\begin{spec}
put  :: s -> v  -> Maybe s
get  :: s       -> Maybe v
\end{spec}
satisfying two well-behavedness laws:
\begin{align}
|put s v| = |Just s'| \quad&\Rightarrow\quad \phantom{|put s v|}\llap{|get s'|} = |Just v| \tag{\textsc{PutGet}} \label{eq:PutGet} \\
|get s| = \rlap{|Just v|}\phantom{|Just s'|} \quad&\Rightarrow\quad |put s v| = |Just s| \tag{\textsc{GetPut}} \label{eq:GetPut}
\end{align}
\end{definition}
In the original formulation~\cite{Lenses}, a lens refers to just a pair of functions having the right types, and one needs to explicitly say ``well-behaved lens'' to mean a well-behaved pair; we will talk about well-behaved lenses only, though, so we build well-behavedness into our definition of lenses.
Also note that this definition models partial transformations explicitly as |Maybe|-valued functions: |put| and |get| are \emph{total} functions that can nevertheless produce |Nothing| to indicate failure.

From this definition of well-behavedness, we can immediately prove what might be called the ``fundamental theorem'' of putback-based bidirectional programming:
\begin{theorem}[uniqueness of {\itshape get}] \label{thm:uniqueness}
Given two lenses whose |put| components are equal, their |get| components are also equal.
\end{theorem}
\begin{proof}
Let $l$~and~$r$ be two lenses; denote their |put|/|get| components as |put l|/|get l| and |put r|/|get r| respectively, and assume that $|put l| = |put r|$.
Then for any $s$~and~$v$,
\begin{align*}
& |get l s| = |Just v| \\
\Leftrightarrow& \reason{well-behavedness of~|l|} \\
& |put l s v| = |Just s| \\
\Leftrightarrow& \reason{$|put l| = |put r|$} \\
& |put r s v| = |Just s| \\
\Leftrightarrow& \reason{well-behavedness of~|r|} \\
& |get r s| = |Just v|
\end{align*}
(This also entails that $|get l s| = |Nothing|$ if and only if $|get r s| = |Nothing|$.) \qed
\end{proof}
The theorem guarantees that the BiGUL programmer is in full control of the bidirectional behavior --- programming the |put| behavior is sufficient to determine the |get| behavior.
Also, to the language designer, the theorem gives a kind of reassurance that, once the |put| behavior of a construct is determined, there is no need to worry about which |get| behavior should be adopted --- there is at most one possibility.
This is in contrast to |get|-based design, in which there are usually more than one viable |put| semantics that can be assigned to a |get|-based construct, and the designer needs to justify the choice or provide several versions.

\subsection{Designing putback-based language components}

Each BiGUL construct is conceived, at the design stage, as a lens (like |Skip| and |Replace|) or a lens \emph{combinator} (like |Case|), which constructs a more complex lens from simpler ones.
The |put| and |get| components of these lenses usually have to be developed together, but for each lens we will employ a more ``|put|-oriented'' design process: We start from an intended |put| behavior, and then add restrictions so that we can find a corresponding |get|.
This does not guarantee that the lenses we arrive at will have a ``strong |put| flavor'' --- that is, some of the lenses will be as suitable for |get|-based programming as for putback-based programming (or even more suitable).
But we will also see that some other lenses are more naturally understood in terms of their |put| behavior.

\subsubsection{{\itshape Replace}.}

The simplest lens is probably |Replace|, which replaces the entire source with the view:
\begin{spec}
put Replace s v = Just v
\end{spec}
Is there a |get| semantics that can be paired with this |put|? Yes, quite obviously --- in fact, \ref{eq:PutGet} directly gives us the definition of |get Replace|:
\begin{spec}
get Replace v = Just v
\end{spec}
We still need to verify \ref{eq:GetPut}, which can be easily checked to be true.

\subsubsection{{\itshape Skip}.}

Coming up next is |Skip|, whose natural behavior is
\begin{spec}
put Skip s v = Just s
\end{spec}
Considering \ref{eq:PutGet}, though, we immediately see that this behavior is too liberal:
If the view is simply thrown away, how can |get Skip| possibly recover it?
One way out is to require that the view is trivial enough such that it can be thrown away and still be recovered, by setting the view type of |Skip| to the unit type~|()|.
Then it is easy for |get Skip| to recover the view, for which there is only one choice:
\begin{spec}
get Skip s = Just ()
\end{spec}
This is the approach adopted prior to BiGUL 1.0.

More generally, we can establish well-behavedness as long as |get Skip| has only one view choice for each source, regardless of what the view type is.
The existence of this ``unique choice'' is witnessed by a function |f :: s -> v|, which we add as an additional argument to |Skip|.
The |get| direction is then
\begin{spec}
get (Skip f) s = Just (f s)
\end{spec}
From the |put| direction, we may think of this function~|f| as specifying a consistency relation, saying that the view information is completely included in the source (since you can compute the view from the source) and can be safely discarded.
|Skip f| can be used if and only if the source and view are consistent in that sense.
We thus arrive at:
\begin{spec}
put (Skip f) s v = if v == f s then return s else Nothing
\end{spec}
This pair of |put| and |get| can be verified to be well-behaved.
|Skip f|, which features in BiGUL 1.0, is one lens which turns out to be more easily understood from the |get| direction --- it bidirectionalizes any function whose codomain has decidable equality, albeit trivially.
We get the first version of |Skip| as a special case by setting~|f| to |const ()|.

\subsubsection{{\itshape Prod}.}

For a simplest example of a lens combinator, we look at |Prod|.
Both the source and view types should be pairs; |Prod| accepts two lenses, say |l|~and~|r|, and applies them respectively to the left and right components:
\begin{spec}
put (l `Prod` r) (sl, sr) (vl, vr) = do  sl'  <- put l  sl  vl
                                         sr'  <- put r  sr  vr
                                         return (sl', sr')
\end{spec}
The |get| direction is unsurprising:
\begin{spec}
get (l `Prod` r) (sl, sr) = do  vl  <- get l  sl
                                vr  <- get r  sr
                                return (vl, vr)
\end{spec}
Having constructed |put| and |get| from |l|~and~|r|, we also expect that their well-behavedness is a consequence of the well-behavedness of |l|~and~|r|.
Intuitively, this pair of |put| and |get| does look well-behaved if |l|~and~|r| are. But how do we establish that formally?
To prove \ref{eq:PutGet}, for example, we should prove from the assumption
\begin{equation}
|put (l `Prod` r) (sl, sr) (vl, vr) = Just (sl', sr')|
\label{eq:Prod-PutGet-assumption}
\end{equation}
the conclusion
\begin{equation}
|get (l `Prod` r) (sl', sr') = Just (vl, vr)|
\label{eq:Prod-PutGet-conclusion}
\end{equation}
Both equations say that a somewhat complicated monadic |Maybe|-program computes successfully to some value.
It may seem that we need some messy case analysis, but what we know about |Maybe|-programs tells us that such a program computes successfully if and only if every step of the program does, and this helps us to break both (\ref{eq:Prod-PutGet-assumption})~and~(\ref{eq:Prod-PutGet-conclusion}) into simpler equations.
Formally, we have this lemma:
\begin{lemma}\label{lem:bind-success}
Let |mx :: Maybe a| and |f :: a -> Maybe b|. Then, for all |y :: b|,
\[ |mx >>= f = Just y| \]
if and only if
\[ |mx = Just x| \quad\text{and}\quad |f x = Just y| \qquad\text{for some |x :: a|} \]
\end{lemma}
\begin{proof}
Case analysis on |mx|. \qed
\end{proof}
This lemma can be nicely applied to |Maybe|-programs written in the |do|-notation, transforming such programs into \emph{predicates} saying that a program computes to some given value.
To do it more formally: Define a translation $\mathcal{S}$ from |do|-blocks of type |Maybe a| to predicates on~|a| by
\begin{align*}
\mathcal S\;(|do { x <- mx; B }|)\;y &~=~ \exists x.\ |mx = Just x| \wedge \mathcal S\;(|do B|)\;y \\
\mathcal S\;(|do { my }|)\;y &~=~ |my = Just y|
\end{align*}
Then we can extend Lemma~\ref{lem:bind-success} to the following:
\begin{lemma} \label{lem:do-success}
The proposition
\[ \mathcal S\;(|do B|)\;y \]
is true if and only if
\[ |do B| = |Just y| \]
\end{lemma}
\begin{proof}
By induction on the list structure of~|B|, using Lemma~\ref{lem:bind-success} repeatedly. \qed
\end{proof}
For example, applying~$\mathcal S$ to |put (l `Prod` r) (sl, sr) (vl, vr)| yields
\begin{align*}
\lambda (sl'', sr'').\
&\exists sl'.\ |put l sl vl = Just sl'| \wedge {} \\
&\exists sr'.\ |put r sr vr = Just sr'| \wedge {} \\
&|return (sl', sr') = Just (sl'', sr'')|
\end{align*}
where the last equation is equivalent to $|sl' = sl''| \wedge |sr' = sr''|$ (since |return = Just| for the |Maybe| monad).
Applying Lemma~\ref{lem:do-success} and doing some simplification, (\ref{eq:Prod-PutGet-assumption})~is equivalent to
\[ |put l sl vl = Just sl'| \quad\wedge\quad |put r sr vr = Just sr'| \]
Similarly, (\ref{eq:Prod-PutGet-conclusion})~can be shown to be equivalent to
\[ |get l sl' = Just vl| \quad\wedge\quad |get r sr' = Just vr| \]
The entailment is then just \ref{eq:PutGet} for |l|~and~|r|.

\subsubsection{{\itshape Case}.} This is a representative combinator in BiGUL, and arguably the most complex one.
For simplicity, let us consider a two-branch variant of |Case| first.
A branch is a condition and a body; since in |put| we manipulate both a source and a view, the conditions in general can be binary predicates on both the source and view.
We thus define the type of branches as:
\begin{spec}
type CaseBranch s v = (s -> v -> Bool, BiGUL s v)
\end{spec}
and consider the following variant of |Case|:
\begin{spec}
Case :: CaseBranch s v -> CaseBranch s v -> BiGUL s v
\end{spec}
The straightforward behavior is
\begin{spec}
put (Case (pl, l) (pr, r)) s v =  if       pl  s v  then  put l  s v
                                  else if  pr  s v  then  put r  s v
                                  else Nothing
\end{spec}
That is, depending on which condition is satisfied (with |pl| having higher priority), we execute either |put l| or |put r|, or fail the computation if neither of the conditions is satisfied.
Now, again, we ask the question: Can we find a |get| behavior to pair with this |put|?

\paragraph{Ruling out branch switching for \ref{eq:PutGet}.} An important working assumption here is that we want lens combinators to be \emph{compositional}:
When we looked at |Prod|, for example, we defined its |put| and |get| in terms of those of the smaller lenses, and derived the overall well-behavedness from that of the smaller lenses.
For |Case|, this implies that, when establishing well-behavedness, we want a |get| following a |put| (or a |put| following a |get|) to use the same branch taken by the |put| (or the |get|), so we can invoke \ref{eq:PutGet} (or \ref{eq:GetPut}) of the branch.
The current |put| behavior of |Case| does not leave any clue in the updated source about which branch is used to produce it, though, so it is impossible for |get| to choose the right branch.

One solution, which does not require changing the syntax of |Case|, is to check that the ranges of the branches are \emph{disjoint}.
In general, for a lens, the range of a |put| can be shown to coincide with the domain of the corresponding |get|.
So the |get| behavior of |Case| can simply try to execute both branches on the input source, and there will be at most one branch that computes successfully.
We can put (expensive) disjointness checks into |put| such that if |put| succeeds, the subsequent |get| will have at most one branch to choose:
\begin{spec}
put (Case (pl, l) (pr, r)) s v =
  if       pl  s v  then  do  s' <- put l  s v
                              maybe (return s') (const Nothing) (get r  s')
  else if  pr  s v  then  do  s' <- put r  s v
                              maybe (return s') (const Nothing) (get l  s')
  else Nothing
\end{spec}
If |get| favors the first branch, meaning that it declares success as soon as the first branch succeeds (without requiring that the second branch fails),
\begin{spec}
get (Case (pl, l) (pr, r)) s = maybe (get r s) return (get l s)
\end{spec}
then we can also omit the check in |put|'s first branch:
\begin{spec}
put (Case (pl, l) (pr, r)) s v =
  if       pl  s v  then  put l  s v
  else if  pr  s v  then  do  s' <- put r  s v
                              maybe (return s') (const Nothing) (get l  s')
  else Nothing
\end{spec}

\paragraph{Ruling out branch switching for \ref{eq:GetPut}.}

The \ref{eq:GetPut} direction, on the other hand, still does not avoid branch switching --- the outcome of |get| does not say anything about which of |pl| and |pr| will be satisfied in the subsequent |put|.
So we add some checks to |get| such that |get|'s success will tell us which branch will be chosen by |put|:
\begin{spec}
get (Case (pl, l) (pr, r)) s = maybe  (do  v <- getBranch (pr, r) s
                                           if pl s v  then  Nothing
                                                      else  return v)
                                      return
                                      (getBranch (pl, l) s)

getBranch (pl, l) s = do  v <- get l s
                          if pl s v  then  return v
                                     else  Nothing
\end{spec}
The definition of |put| should also be revised to use |getBranch| for disjointness check.
But this breaks \ref{eq:PutGet}! Since |put| does not guarantee that the updated source and the view satisfy the condition of the branch executed, even though |get| will be able to choose the right branch, the subsequent, newly added check is not guaranteed to succeed.
We thus also need to add similar checks to |put|:
\begin{spec}
put (Case (pl, l) (pr, r)) s v =
  if       pl  s v  then  do  s' <- put l  s v
                              if pl s' v  then  return s'
                                          else  Nothing
  else if  pr  s v  then  do  s' <- put r  s v
                              if pr s' v  then  maybe  (return s')
                                                       (const Nothing)
                                                       (getBranch (pl, l)  s')
                                          else  Nothing
  else Nothing
\end{spec}
Now this pair of |put| and |get| can be verified to be well-behaved.

\paragraph{Improving the efficiency of |get|.}

The efficiency of the current |get| does not seem very good, especially when, in general, any number of branches is allowed, and |get| has to try to execute each branch, possibly with a high cost, until it reaches a successful one; also, inefficient |get| affects the efficiency of |put|, which calls |get| to check range disjointness.
An idea is to ask the programmer to make a rough ``prediction'' of the range of each branch:
We enrich |CaseBranch| with a third component, which is a source predicate:
\begin{spec}
type CaseBranch s v = (s -> v -> Bool, BiGUL s v, s -> Bool)
\end{spec}
This new predicate is supposed to be satisfied by the updated source; we again add checks to |put| to ensure this:
\begin{spec}
put (Case (pl, l, ql) (pr, r, qr)) s v =
  if       pl  s v  then  do  s' <- put l  s v
                              if pl s' v && ql s'  then  return s'
                                                   else  Nothing
  else if  pr  s v  then  do  s' <- put r  s v
                              if pr s' v && qr s'
                                then  maybe  (return s')
                                             (const Nothing)
                                             (getBranch (pl, l, ql)  s')
                                else  Nothing
  else Nothing
\end{spec}
Let us call |pl| and |pr| the \emph{main conditions}, and |ql| and |qr| the \emph{exit conditions}.
The exit condition, in general, over-approximates the range of a branch.
In other words, in the |get| direction, every source in the domain of a branch satisfies the exit condition.
Contrapositively, if a source does not satisfy the exit condition, then |get| for that branch will necessarily fail, and we do not need to try to execute the branch at all.
This leads to the following revised definition of |getBranch|:
\begin{spec}
getBranch (pl, l, ql) s = if ql s  then  do  v <- get l s
                                             if pl s v  then  return v
                                                        else  Nothing
                                   else  Nothing
\end{spec}
If we do not care about efficiency, we can simply use |const True| as exit conditions, and the behavior is then exactly the same as the previous version.
But if we supply disjoint exit conditions, then |get| will try at most one branch.
Incidentally (but actually no less importantly), making exit conditions explicit also encourages the programmer to think about range disjointness, which is essential to totality of |Case|.

\paragraph{Adaptation.}

We have seen that, to make |Case| total, one thing we need to ensure is that the main condition of a branch should be satisfied again after the update.
In practice, the main condition is usually closely related to the consistency relation, and we will only be able to deal with sources and views that are already more or less consistent; this is a rather severe restriction.
As we have seen, the solution is to introduce a different kind of branches called \emph{adaptive branches}, which can deal with sources and views that are too inconsistent by adapting the source to establish enough consistency such that a normal branch becomes applicable.
Again, for simplicity, we consider only a variant of |Case| which has just one adaptive branch at the end:
\begin{spec}
type CaseAdaptiveBranch s v = (s -> v -> Bool, s -> v -> s)

Case ::  CaseBranch s v -> CaseBranch s v ->
         CaseAdaptiveBranch s v -> BiGUL s v
\end{spec}
The execution structure of |put| becomes slightly more complicated, as the whole thing has to be run again after adaptation; to ensure termination, we require that the second run cannot match an adaptive branch again.
This is realized in BiGUL in continuation-passing style:
\begin{spec}
put (Case bl br ba) s v =
  putWithAdaptation bl br ba s v (\sa ->
    putWithAdaptation bl br ba sa v (const Nothing))

putWithAdaptation ::
  CaseBranch s v -> CaseBranch s v -> CaseAdaptiveBranch s v ->
  s -> v -> (s -> Maybe s) -> Maybe s
putWithAdaptation (pl, l, ql) (pr, r, qr) (pa, f) s v cont =
  if       pl  s v  then  do  s' <- put l  s v
                              if pl s' v && ql s'  then  return s'
                                                   else  Nothing
  else if  pr  s v  then  do  s' <- put r  s v
                              if pr s' v && qr s'
                                then  maybe  (return s')
                                             (const Nothing)
                                             (getBranch (pl, l, ql)  s')
                                else  Nothing
  else if  pa  s v  then  cont (f s v)
  else  Nothing
\end{spec}

What about |get|?
It turns out that |get| can simply ignore the adaptive branch!
If you have doubt about this ``choice'', just invoke the fundamental theorem (Theorem~\ref{thm:uniqueness}): The |put| behavior is exactly what we want, and we can verify that the pair of |put| and |get| is well-behaved, so we are reassured that our ``choice'' is ``correct'', simply because there is no other choice of |get|.

To sum up, we have arrived at a simpler variant of |Case| which nevertheless has all the features of the multi-branch |Case| in BiGUL.
We have inserted various dynamic checks into the |put| semantics, and the BiGUL programmer needs to be aware of these constraints to make execution of |Case| succeed:
For each normal branch, (i)~the main condition should be satisfied after the update,
(ii)~the main conditions of the branches before this one should not be satisfied after the update, and
(iii)~the exit condition should be satisfied by the updated source.
Also the ranges of all the normal branches should be disjoint; the programmer is encouraged to write disjoint exit conditions, which imply disjointness of the ranges, and improve the efficiency of |get|.
Also, for each adaptive branch, the adapted source and the view should match the main condition of a normal branch.

\subsubsection{{\itshape RearrV}.}

Source and view rearrangements are also among the more complex constructs of BiGUL.
Their complexity lies in the strongly and generically typed treatment of pattern matching, though, rather than their bidirectional behavior.
The two kinds of rearrangements are fairly similar, and we will discuss view rearrangement only.

Pattern matching is inherently a bidirectional operation:
In one direction, we break something into a collection of its components at the variable positions of a pattern.
This collection can be considered as indexed by the variable positions, and acting like an \emph{environment} for expression evaluation.
Indeed, conversely, if we have a pattern and a corresponding environment, we can treat the pattern as an expression and evaluate it under the environment.
These two directions are inverse to each other, i.e., they form an isomorphism.
For the language designer, it may be slightly tedious to establish such isomorphisms, but for the programmer, pattern matching and evaluation are arguably the most natural way to decompose and rearrange things.
Previous bidirectional languages usually provide theoretically simpler combinators for decomposition and rearrangement, but they are hard to use in practice.
BiGUL's support of pattern matching, on the other hand, turns out to be one important contributing factor in its usability.

BiGUL's patterns are strongly typed: The programmer has to declare a target type for a pattern, and the pattern is guaranteed by typechecking to make sense for that target type.
This can be achieved by defining the datatype of patterns as a generalised algebraic datatype:
\begin{spec}
data Pat a where
  PVar    ::  Eq a => Pat a
  PConst  ::  Eq a => a -> Pat a
  PProd   ::  Pat a -> Pat b -> Pat (a, b)
  PLeft   ::  Pat a -> Pat (Either a b)
  PRight  ::  Pat b -> Pat (Either a b)
  PIn     ::  InOut a => Pat (F a) -> Pat a
\end{spec}
A pattern can be a (nameless) variable, a constant, a product, a |Left| or |Right| injection (for the |Either| type), or a generic constructor, and its target type is given as the index in its type.
So, for example, |PProd| cannot be used to match an |Either| value.
The |InOut| typeclass contains the types which can be broken into a sum-of-products representation.
For example, |[a]| is an instance of |InOut|, and |F [a]|, an isomorphic sum-of-products representation of |[a]|, is |Either () (a, [a])|.
The isomorphism is witnessed by
\[ |inn :: InOut a => F a -> a| \qquad\text{and}\qquad |out :: InOut a => a -> F a| \]
These two functions will be used to define pattern matching and evaluation.

How do we define pattern matching?
The result of a pattern matching, as we mentioned above, is an environment indexed by the variable positions of the pattern.
Here we want a safe (but not necessarily efficient) representation of the environment type, in the sense that the indexes into the environment should be exactly the variable positions of the pattern, which is enforced statically by typechecking.
In other words, this type depends on the pattern, and a way to compute this type is to encode it as a second index of the |Pat| datatype:
\begin{spec}
data Pat a env where
  PVar    ::  Eq a => Pat a (Var a)
  PConst  ::  Eq a => a -> Pat a ()
  PProd   ::  Pat a  a'  -> Pat b b' b'' -> Pat (a, b) (a', b')
  PLeft   ::  Pat a  a'  -> Pat (Either a b) a'
  PRight  ::  Pat b  b'  -> Pat (Either a b) b'
  PIn     ::  InOut a => Pat (F a) b c -> Pat a b
\end{spec}
Notice that an environment type is just a product of |Var| types.
We will talk about |Var| later, which is simply defined by
\begin{spec}
newtype Var a = Var a
\end{spec}
Now we can define the pattern matching operation:
\begin{spec}
deconstruct :: Pat a env -> a -> Maybe env
deconstruct PVar           x          = return (Var x)
deconstruct (PConst c)     x          = if c == x then return () else Nothing
deconstruct (l `PProd` r)  (x, y)     = liftM2 (,)  (deconstruct l  x  )
                                                    (deconstruct r  y  )
deconstruct (PLeft  p)     (Left  x)  = deconstruct p x
deconstruct (PLeft _)      _          = Nothing
deconstruct (PRight p)     (Right x)  = deconstruct p x
deconstruct (PRight _)     _          = Nothing
deconstruct (PIn p)        x          = deconstruct p (out x)
\end{spec}
and its inverse (which is total):
\begin{spec}
construct :: Pat a env -> env -> a
construct PVar           (Var x)       = x
construct (PConst c)     _             = c
construct (l `PProd` r)  (envl, envr)  = (construct l envl, construct r envr)
construct (PLeft  p)     env           = Left   (construct p env)
construct (PRight p)     env           = Right  (construct p env)
construct (PIn p)        env           = inn (construct p env)
\end{spec}

Now consider view rearrangement, which evaluates a ``simple'' pattern-matching $\lambda$-expression on the view and continue updating with the transformed view.
The body of the $\lambda$-expression refers to the variables appearing in the pattern.
How do we represent such references?
We have seen that an environment type is a product, i.e., a binary tree; to refer to a component in an environment, we can use a \emph{path} that goes from the root to a sub-tree.
In BiGUL, these paths are called \emph{directions}:
\begin{spec}
data Direction env a where
  DVar    ::  Direction (Var a) a
  DLeft   ::  Direction a  t -> Direction (a, b) t
  DRight  ::  Direction b  t -> Direction (a, b) t
\end{spec}
The type of a direction is indexed by the environment type it points into and the component type it points to.
Note that the type of |DVar| is specified to work with only environment types marked with |Var|; this is for ensuring that a direction goes all the way down to an actual component at a variable position of the pattern, rather than stopping half-way, pointing to a sub-tree which include more than one component.
It is easy to extract a component from an environment following a direction:
\begin{spec}
retrieve :: Direction env a -> env -> a
retrieve  DVar        (Var x)  = x
retrieve (DLeft   d)  (x, _)   = retrieve d x
retrieve (DRight  d)  (_, y)   = retrieve d y
\end{spec}
Now we can define \emph{expressions}, which are similar to patterns but include directions rather than variables, to represent the body of rearranging $\lambda$-expressions:
\begin{spec}
data Expr env a where
  EDir    ::  Direction env a -> Expr env a
  EConst  ::  (Eq a) => a -> Expr env a
  EProd   ::  Expr env a  -> Expr env b -> Expr env (a, b)
  ELeft   ::  Expr env a  -> Expr env (Either a b)
  ERight  ::  Expr env b  -> Expr env (Either a b)
  EIn     ::  (InOut a) => Expr env (F a) -> Expr env a
\end{spec}
Evaluating an expression under an environment is similar to inverse pattern matching:
\begin{spec}
eval :: Expr env a -> env -> a
eval (EDir d)       env = retrieve d env
eval (EConst c)     env = c
eval (l `EProd` r)  env = (eval l env, eval r env)
eval (ELeft  e)     env = Left   (eval e env)
eval (ERight e)     env = Right  (eval e env)
eval (EIn e)        env = inn (eval e env)
\end{spec}
The type of |RearrV| is then:
\begin{spec}
RearrV :: Pat v env -> Expr env v' -> BiGUL s v' -> BiGUL s v
\end{spec}
And its |put| behavior is simply:
\begin{spec}
put (RearrV p e b) s v = do  env <- deconstruct p v
                             put b s (eval e env)
\end{spec}

For the |get| direction, after executing the inner BiGUL program to obtain an intermediate view, we should reverse the roles of the pattern and body in the $\lambda$-expression, using the latter as a pattern to match the intermediate view.
This intermediate view will be decomposed, and eventually each of its components will be paired with a direction indicating which variable position the component should go into.
We can prepare a ``container'' shaped like the pattern, whose variable positions are initially empty.
Whenever we reach a component and a direction, we try to put that component into the place in the container pointed to by the direction; if two components are put into the same position twice (indicating that the $\lambda$-expression uses a variable more than once), then they must be equal.
In the end, all places in the container must be filled before it can be used as an environment to evaluate the pattern.
Again, to compute the type of containers from a pattern, we add a third index to |Pat|:
\begin{spec}
data Pat a env con where
  PVar    ::  Eq a => Pat a (Var a) (Maybe a)
  PConst  ::  Eq a => a -> Pat a () ()
  PProd   ::  Pat a  a'  a''  -> Pat b b' b'' -> Pat (a, b) (a', b') (a'', b'')
  PLeft   ::  Pat a  a'  a''  -> Pat (Either a b) a'  a''
  PRight  ::  Pat b  b'  b''  -> Pat (Either a b) b'  b''
  PIn     ::  InOut a => Pat (F a) b c -> Pat a b c
\end{spec}
A container type is just like an environment type except that the variable positions give rise to |Maybe| instead of |Var|.
The first step --- matching a value with an \emph{expression} --- can then be implemented as:
\begin{spec}
uneval :: Pat a env con -> Expr env b -> b -> con -> Maybe con
uneval p (EDir d)     x          con = unevalDir p d x con
uneval p (EConst c)   x          con = if c == x then return con else Nothing
uneval p (EProd l r)  (x, y)     con = uneval p l x con >>= uneval p r y
uneval p (ELeft  e)   (Left  x)  con = uneval p e x con
uneval p (ELeft _)    x          con = Nothing
uneval p (ERight e)   (Right x)  con = uneval p e x con
uneval p (ERight _)   x          con = Nothing
uneval p (EIn e)      x          con = uneval p e (out x) con

unevalDir :: Pat a env con -> Direction env b -> b -> con -> Maybe con
unevalDir PVar           DVar         x  (Just y)      =  if x == y
                                                          then return (Just x)
                                                          else Nothing
unevalDir PVar           DVar         x  Nothing       =  return (Just x)
unevalDir (PConst c)     _            x  con           =  return con
unevalDir (l `PProd` r)  (DLeft   d)  x  (conl, conr)  =  liftM (, conr)
                                                            (unevalDir l d x conl)
unevalDir (l `PProd` r)  (DRight  d)  x  (conl, conr)  =  liftM (conl ,)
                                                            (unevalDir r d x conr)
unevalDir (PLeft   p)    d            x  con           =  unevalDir p d x con
unevalDir (PRight  p)    d            x  con           =  unevalDir p d x con
unevalDir (PIn p)        d            x  con           =  unevalDir p d x con
\end{spec}
This function |uneval| initially takes an empty container, which is generated by:
\begin{spec}
emptyContainer :: Pat v env con -> con
emptyContainer PVar           = Nothing
emptyContainer (PConst c)     = ()
emptyContainer (l `PProd` r)  = (emptyContainer l, emptyContainer r)
emptyContainer (PLeft   p)    = emptyContainer p
emptyContainer (PRight  p)    = emptyContainer p
emptyContainer (PIn p)        = emptyContainer p
\end{spec}
And then we can try to convert a container to an environment, checking whether the container is full in the process:
\begin{spec}
fromContainerV :: Pat v env con -> con -> Maybe env
fromContainerV PVar           Nothing       =  Nothing
fromContainerV PVar           (Just v)      =  return (Var v)
fromContainerV (PConst c)     con           =  return ()
fromContainerV (l `PProd` r)  (conl, conr)  =  liftM2 (,)
                                                 (fromContainerV l  conl  )
                                                 (fromContainerV r  conr  )
fromContainerV (PLeft   p)    con           =  fromContainerV pat con
fromContainerV (PRight  p)    con           =  fromContainerV pat con
fromContainerV (PIn p)        con           =  fromContainerV pat con
\end{spec}
If we can get hold of an environment, then we can let out a sigh of relief, since the last step --- inverse pattern matching --- is total.
To sum up:
\begin{spec}
get (RearrV p e b)  s = do  v'   <- get b s
                            con  <- uneval p e v' (emptyContainer p)
                            env  <- fromContainerV p con
                            return (construct p env)
\end{spec}
Conceptually, this is just reversing pattern matching and expression evaluation. To actually prove the well-behavedness, though, we need to reason about stateful computation (which is what |uneval| essentially is), which involves coming up with suitable invariants and proving that they are maintained throughout the computation.
It is somewhat tedious, but can be done without a problem.

It is interesting to mention that there would be a catch if we designed this combinator from the |get| direction: It is tempting to think that a rearranging $\lambda$-expression gives rise to an isomorphism, which can be lifted to a lens, and can be composed with the inner lens to give a lens semantics to |RearrV|.
This would result in a redundant computation of an intermediate source which is immediately discarded, and now the success of the whole computation would unnecessarily depend on that of the intermediate source.
To eliminate the redundant computation, we would need to use a special composition which composes a lens with an isomorphism on the right.
Such a need would be hard to notice since the |get| behavior of the two compositions are the same; that is, we really have to think in terms of |put| to see that the special composition is needed.




















