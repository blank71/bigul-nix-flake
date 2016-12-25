%include lhs2TeX-macros.lhs

\section{Putback-based bidirectional programming}

A {\em bidirectional transformation} basically consists of a pair of
transformations: the {\em forward} transformation |get s| is used to
produce a target view |v| from a source |s|, while the {\em putback}
transformation |put s v| is used to reflect modifications on the view
|v| to the source |s|.  These two transformations should be {\em
well-behaved} in the sense that they satisfy the following
round-tripping laws.
\begin{align*}
\tag*{\textsc{GetPut}}
\label{GetPut}
|put s (get s)  = s|\\
\tag*{\textsc{PutGet}}
\label{PutGet}
|get (put s v)  = v|
\end{align*}
The \ref{GetPut} property requires that no changing on the view shall
be reflected as no changing on the source, while the \ref{PutGet}
property requires all changes in the view to be completely reflected
to the source so that the changed view can be computed again by
applying the forward transformation to

{\em Bidirectional programming} is to develop well-behaved
bidirectional transformations (BXs) to solve various synchronization
problems.  A straightforward approach to bidirectional programming is
to write two unidirectional transformations. Although this ad-hoc
solution provides full control over both get and putback
transformations and can be realized using standard programming
languages, the programmer needs to show that the two transformations
satisfy the well-behavedness laws, and a modification to one of the
transformations requires a redefinition of the other transformation as
well as a new well-behavedness proof.
To ease and enable maintainable bidirectional programming, it is
preferable to write just a single program that can denote both
transformations.

Lots of work \cite{Lenses,Bohannon:06,Bohannon:08,Hofmann:2011,XLHZ07,MHNHT07,Voigt09,Hidaka:10} has been devoted to the {\em get-based}
approach, allowing users to write the forward
transformation |get| and deriving a suitable putback transformation.
While the get-based approach is friendly, 
a |get| function may not be injective, so there may exist
many possible |put| functions that can be combined with it to form a
valid BX and there is no way to control the choice of |put| through
the definition of |get|. 
This ambiguity of put is what makes bidirectional
programming challenging and unpredictable in practice.

The main topic of this tutorial is the {\em putback-based} approach
to bidirectional programming.
In contrast to the get-based approach, it allows users to write the backward 
transformation |put| and derives a suitable |get| that can be
paired with |put| to form a bidirectional transformation if it exists.
Interestingly, while |get| usually loses information
when mapping from a source to a view, |put| must preserve information
when putting back from the view to the source, according to the
\ref{PutGet} property.

Before explaining how to write |put|, let us briefly review
the foundation~\cite{Foster:09,FiHP15,FiHP15b}, showing that "putback"
is the essence of bidirectional programming.
We start by defining validity of |put| as follows.

\begin{definition}[Validity of |put|]
We say that a |put| is {\em valid} if there exists a |get|
such that both \ref{GetPut} and \ref{PutGet} are satisfied. 
\end{definition}

The first interesting fact is that, for a valid |put|, there exists at most one |get|
that can form a BX with it. This is in sharp contrast to get-based 
bidirectional programming, where many |put|s may be paired with a |get|
to form a BX. 

\begin{lemma}[Uniqueness of |get|]
\label{lemma:injective}
Given a |put| function, there exists at most 
one |get| function that forms a well-behaved BX.
\end{lemma}

The second interesting fact is that it is possible to
check validity of |put| without mentioning |get|.
The following are two important properties on |put|.
\begin{itemize}
\item 
 The first, which we call \emph{view determination}, says that equivalence 
of updated sources produced by a |put| implies equivalence of views that are put back.
\begin{align*}
	\label{PutDet}
	\tag*{\textsc{ViewDetermination}}
	\forall~s,s',v,v'.~put~s~v~=~put~s'~v'~\Rightarrow~v~=~v'
\end{align*}
Note that the view determination implies that |put s| is injective (with |s=s'|).

\item The second, which we call \emph{source stability}, denotes a slightly stronger notion of surjectivity for every source:
\begin{align*}
	\label{PutStable}
	\tag*{\textsc{SourceStability}}
	\forall~s.~\exists~v.~put~s~v~=~s
\end{align*}
\end{itemize}
Actually, these two properties together provide an equivalent characterization of 
the validity of |put|. 
\begin{theorem}
\label{th:put2}
A |put| function is valid if and only if it satisfies the \ref{PutDet} and \ref{PutStable} properties. 
\end{theorem}

Practically, there are few languages supporting put-based
bidirectional programming. This is not without reason: as argued in
\cite{Foster:09}, it is far from being straightforward to construct a
framework that can directly support putback-based bidirectional
programming.

This tutorial introduces BiGUL \cite{KoZH16}, a simple but powerful
putback-based bidirectional language,
which grew out of the work \cite{PaHF14,PaZH14}.
We shall demonstrate how to program with BiGUL, explain the
principle behind BiGUL, and show its applications in
developing various bidirectional transformations.





