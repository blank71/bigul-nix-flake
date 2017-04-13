% !TEX root = paper.tex

%include lhs2TeX-macros.lhs

\section{Putback-based bidirectional programming}
\label{sec:PutBX}

In this tutorial, the kind of bidirectional transformations (BXs) we discuss is \emph{aymmetric lenses}~\cite{Lenses},
which basically consist of a pair of transformations:
a {\em forward} transformation |get| producing a \emph{view} from a \emph{source}, and a {\em backward}, or {\em putback},
transformation |put| which takes a source and a possibly modified view, and reflects the modifications on the view to the source, producing an updated source.
These two transformations should be {\em
well-behaved} in the sense that they satisfy the following
round-tripping laws:
\begin{align*}
\tag*{\textsc{GetPut}}
\label{GetPut}
|put s (get s)  = s|\\
\tag*{\textsc{PutGet}}
\label{PutGet}
|get (put s v)  = v|
\end{align*}
The \ref{GetPut} property requires that no change to the view should
be reflected as no change to the source, while the \ref{PutGet}
property requires that all changes in the view should be completely reflected
to the source so that the changed view can be successfully recovered by
applying the forward transformation to the updated source.

The purpose of {\em bidirectional programming} is to develop well-behaved
bidirectional transformations to solve various synchronization
problems.  A straightforward approach to bidirectional programming is
to write two unidirectional transformations. Although this ad hoc
solution provides full control over both get and putback
transformations, and can be realized using standard programming
languages, the programmer needs to show that the two transformations
satisfy the well-behavedness laws, and a modification to one of the
transformations requires a redefinition of the other transformation as
well as a new well-behavedness proof.
To ease and enable maintainable bidirectional programming, it is
preferable to write just a single program that can denote both
transformations.

Lots of work \cite{Lenses,Bohannon:06,Bohannon:08,Hofmann:2011,XLHZ07,MHNHT07,Voigt09,Hidaka:10} has been devoted to the {\em get-based}
approach, allowing the programmer to write the forward
transformation |get| and deriving a suitable putback transformation.
While the get-based approach is friendly\todo{Tony: What is meant by friendly? Why?}, 
a |get| function will typically not be injective, so there may exist
many possible |put| functions that can be combined with it to form a
valid BX, and there is no way to control the choice of |put| through
the definition of |get|. 
This ambiguity of |put| is what makes bidirectional
programming challenging and unpredictable in practice.

\todo{Tony: Just wondering...  if get-based approaches are called "get-based", why is the put-based approach called "putback-based"?  If there is a good reason for this then it would certainly be interesting for the (novice) reader such as myself.}

The main topic of this tutorial is the {\em putback-based} approach
to bidirectional programming.
In contrast to the get-based approach, it allows the programmer to write a backward 
transformation |put| and derives a suitable |get| that can be
paired with this |put| to form a bidirectional transformation.
Interestingly\todo{Tony I'm not sure I understand why this is particularly "interesting".}, while |get| usually loses information
when mapping from a source to a view, |put| must preserve information
when putting back from the view to the source, according to the
\ref{PutGet} property.

Before explaining how to program |put| in practice, let us briefly review
the foundations~\cite{Foster:09,FiHP15,FiHP15b}, showing that ``putback''
is the essence of bidirectional programming.
We start by defining validity of |put| as follows:

\begin{definition}[Validity of |put|]
We say that a |put| function is {\em valid} if there exists a |get| function
such that both \ref{GetPut} and \ref{PutGet} are satisfied. 
\end{definition}

The first interesting fact is that, for a valid |put|, there exists exactly one |get|
that can form a BX with it. This is in sharp contrast to get-based 
bidirectional programming, where many |put|s may be paired with a |get|
to form a BX. 

\begin{lemma}[Uniqueness of |get|]
\label{lemma:injective}
Given a |put| function, there exists at most 
one |get| function that forms a well-behaved BX.
\end{lemma}

\todo{Tony: How about the proof?  To hard? To obvious?  I wouldn't have minded having it here.}

The second interesting fact is that it is possible to
check the validity of |put| without mentioning |get|.
The following are two important properties of |put|.
\begin{itemize}
\item 
 The first, which we call \emph{view determination}, says that the equivalence 
of updated sources produced by a |put| implies equivalence of views that are put back.
\begin{align*}
	\label{PutDet}
	\tag*{\textsc{ViewDetermination}}
	\forall~s,s',v,v'.~put~s~v~=~put~s'~v'~\Rightarrow~v~=~v'
\end{align*}
Note that view determination implies that |put s| is injective (with |s=s'|).

\item The second, which we call \emph{source stability}, denotes a slightly stronger notion of surjectivity for every source:
\begin{align*}
	\label{PutStable}
	\tag*{\textsc{SourceStability}}
	\forall~s.~\exists~v.~put~s~v~=~s
\end{align*}
\end{itemize}
These two properties together provide an equivalent characterization of 
the validity of |put| \cite{FiHP15b}. 
\begin{theorem}
\label{th:put2}
A |put| function is valid if and only if it satisfies \ref{PutDet} and \ref{PutStable}. 
\end{theorem}

\todo{Tony: Are the proofs for this coming later in the tutorial?  Or is the reader expected to work this out themselves (I didn't try).}

Practically, there are few languages supporting putback-based
bidirectional programming. This is not without reason: as argued by Foster~\cite{Foster:09},
it is more difficult to construct a
framework that can directly support putback-based bidirectional
programming.\todo{Tony: Why?}

In the rest of this tutorial, we will introduce BiGUL~\cite{KoZH16} (pronounced ``beagle''),
a simple yet powerful putback-based bidirectional language,
which grew out of some prior putback-based languages~\cite{PaHF14,PaZH14}.
BiGUL is implemented as an embedded language in Haskell, and we will assume that the reader is reasonably familiar with Haskell.
After briefly explaining how to install BiGUL in Section~\ref{sec:install}, we will introduce basic BiGUL programming in Section~\ref{sec:tour}, and see a few more examples about lists in Section~\ref{sec:lists}.
We will then move on to the underlying principles in Section~\ref{sec:bidirectionality}, explaining the design and implementation of BiGUL in detail.
The last three sections will show how various bidirectional applications can be developed, including list alignment in Section~\ref{sec:alignment}, relational database updating in Section~\ref{sec:Brul}, and parsing and ``reflective'' printing in Section~\ref{sec:BiYacc}.





