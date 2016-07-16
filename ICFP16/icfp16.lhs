\documentclass[numbers]{sigplanconf}

\newif\ifanonymous

\anonymoustrue
%\anonymousfalse

%include polycode.fmt
%
%format ==> = "\Longrightarrow"
%format `Prod`=" \times "
%format V1="V_1"
%format V2="V_2"
%format v1="v_1"
%format v2="v_2"
%format l0="l_0"
%format r0="r_0"
%format i0="i_0"
%format i1="i_1"
%format delta="\delta"
%format delta1="\delta^\prime"
%format d1="\delta_1"
%format d2="\delta_2"
%format d3="\delta_3"
%format Prelude.map=map
%format Prelude.filter=filter
%format Prelude.fmap=fmap
%format Set.map=map
%format Set.findMin=findMin
%format Set.fromList=
%format Set.elems=elems
%format Set.empty=" \emptyset "
%format def="\text{def.}"
%format GetPut="\text{\textsc{GetPut}}"
%format PutGet="\text{\textsc{PutGet}}"

\usepackage{amsmath,amssymb,amsfonts}
\usepackage{graphicx}
\usepackage{xcolor}
\usepackage{xspace}
\usepackage{verbatim}
\usepackage{listings}
\newcommand{\lstcontinueline}{\ensuremath{\hookleftarrow}}
\lstset{%
	basicstyle=\scriptsize\ttfamily,
	language={Haskell},
	inputencoding=utf8,
	breaklines=true,
	prebreak = \raisebox{0ex}[0ex][0ex]{\lstcontinueline},
	morekeywords={},
	deletekeywords={Num,fst},
	keywordstyle=\color[rgb]{0,0,1},             % keywords
	commentstyle=\color[rgb]{0.133,0.545,0.133}, % comments
	stringstyle=\color[rgb]{0.627,0.126,0.941},  % strings
	escapechar=@@,
}
\usepackage{array}
\usepackage{tikz}
\usetikzlibrary{arrows,positioning,
  shapes.multipart,
  matrix,
  positioning,
  shapes.callouts,
  shapes.arrows,
  calc}

\newcommand{\TODO}[1]{{\color{black!10!blue}TODO #1}}
\newcommand{\mydraft}[1]{{\color{black!50!green}#1}}
\newcommand{\mywrong}[1]{{\color{black!10!red}#1}}

\DeclareMathOperator{\where}{where}
\DeclareMathOperator{\bxget}{get}
\DeclareMathOperator{\bxput}{put}
\DeclareMathOperator{\bxcreate}{create}
\DeclareMathOperator{\dput}{dput}
\DeclareMathOperator{\dcreate}{dcreate}
\DeclareMathOperator{\data}{data}
\DeclareMathOperator{\shape}{shape}
\DeclareMathOperator{\recover}{recover}
\DeclareMathOperator{\locs}{locs}

\begin{document}

\special{papersize=8.5in,11in}
\setlength{\pdfpageheight}{\paperheight}
\setlength{\pdfpagewidth}{\paperwidth}

\toappear{}

%\conferenceinfo{CONF 'yy}{Month d--d, 20yy, City, ST, Country}
%\copyrightyear{20yy}
%\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
%\copyrightdoi{nnnnnnn.nnnnnnn}

% Uncomment the publication rights you want to use.
%\publicationrights{transferred}
%\publicationrights{licensed}     % this is the default
%\publicationrights{author-pays}

%\titlebanner{banner above paper title}        % These are ignored unless
%\preprintfooter{short description of paper}   % 'preprint' option specified.

\title{The Under-Appreciated Put: Implementing Delta-Alignment in BiGUL}
\subtitle{A POPL Pearl Submission}

\ifanonymous
\authorinfo{}{}{}
\else
\authorinfo{Jorge Mendes}
           {\hspace{-.5cm}HASLab, INESC TEC \& Universidade do Minho, Portugal\hspace{-.5cm}}
           {jorgemendes@@di.uminho.pt}
\authorinfo{Hsiang-Shang Ko \and Zhenjiang Hu}
           {National Institute of Informatics, Japan}
           {\{hsiang-shang,hu\}@@nii.ac.jp}
\fi

\maketitle

\begin{abstract}
There are two approaches to bidirectional programming:
One is the get-based method where one writes |get|, and
|put| is automatically derived; the other is
the put-based method where one writes |put| and
|get| is automatically derived.
In this paper, we argue that the put-based method
deserves more attention, because
a good language for programming |put| can not only
give full control over the behavior of bidirectional transformations,
but also enable us to efficiently
develop various domain-specific bidirectional languages and use
them seamlessly in one framework, which
would be nontrivial with the get-based method.
We demonstrate how the matching/delta/generic lenses can be
implemented in BiGUL, a putback-based
bidirectional language embedded in Haskell.
\end{abstract}

%\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore,
% you may leave them out
%\terms
%term1, term2

%\keywords
%keyword1, keyword2

%%%
%%% Haskell Preamble
%%%
\begin{comment}
\begin{code}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
module ICFP16 where

import Data.Relation (rngOf)
import Data.Set as Set
import Data.Shape
import Generics.BiGUL.AST
import Generics.BiGUL.Interpreter.Unsafe (get, put)
import Generics.BiGUL.TH
import GHC.Generics
import Prelude hiding (traverse)

import Generics.Pointless.Combinators hiding (and)
import Generics.Pointless.Functors hiding (Functor, (:+:), (:*:))
import Generics.Pointless.HFunctors

infixr 0 ==>
(==>) :: (a -> b) -> a -> b
(==>) = ($)

\end{code}
\end{comment}

\section{Introduction}

Bidirectional transformations are hot! They
originated from the {\em view updating\/} mechanism in the
database community~\cite{Bancilhon:81,Dayal:82,GoPZ88},
and have been attracting a lot of attention
from researchers in the communities of programming languages and 
software engineering \cite{GRACE:09,HSST11},
since the pioneering work of Foster {et al.} on 
a combinatorial language for bidirectional tree transformations \cite{Foster2007}.

A bidirectional transformation (BX for short) is simply
a pair of functions
< get  :: Source -> View
< put  :: Source -> View -> Source
where 
the \emph{get} function extracts a view from a source and the \emph{put}
function updates the original source with information from the new view.
As a simple example, suppose that we wish to synchronize between
rectangles and their heights. We can define
< getHeight  (height, width)          = height
< putHeight  (height, width) height'  = (height', width)
where a rectangle is represented by a pair of its height and width.

Certainly not any pair of |get| and |put| can form bidirectional
transformations for synchronization. |get| and |put| should
satisfy the {\em well-behavedness} laws:
\begin{align*}
\tag*{\textsc{GetPut}}
\label{GetPut}
|put s (get s)  = s|\\
\tag*{\textsc{PutGet}}
\label{PutGet}
|get (put s v)  = v|
\end{align*}
%
The \ref{GetPut} law requires that no changing on the view shall be reflected as
 no changing on the source, while the \ref{PutGet} law requires all changes 
in the view to be completely reflected to the source so that the changed
view can be computed again by applying the forward transformation to
the changed source.
For instance, if we change the above |put| to
< putHeight' (height, width) height' = (height'+1, width)
|get| and |put'| will break the laws.

A straightforward approach to developing well-behaved 
BXs in order to solve various synchronization problems
is to write both |get| and |put|. The approach
has the practical problem that the programmer needs to show that the two transformations
satisfy the well-behavedness laws,
and a modification to
one of the transformations requires a redefinition of the other
transformation as well as a new well-behavedness proof.
To ease and enable maintainable bidirectional programming,
it is preferable to write 
just a single program that can denote both transformations,
which has motivated two different approaches:
\begin{itemize}
\item {\em Get-based method}: allowing users to write |get|
and derive a suitable |put| \cite{Foster2007,MHNHT07,Bohannon:08,Barbosa2010,Hidaka:10,Hofmann2012,Pacheco2012};
\item {\em Put-based method}: allowing users to write |put|
and derive the unique |get| if there is one \cite{PaHF14,PachecoZH14,HuPF14,FischerHP15,Ko2016}.
\end{itemize}

The get-based method has been intensively studied for over ten years
and got much appreciated. It is attractive, because |get| is easy to write,
and if the system knows how to derive a |put|, there would be no additional
burden for users to go from unidirectional to bidirectional.
In contrast, the put-based method is new and far from being appreciated.
One main criticism is that |put| is more difficult to write than |get|.

However, the get-based method hardly describes the full behavior
of a bidirectional transformation, so automatically
derived |put| may not match the programmers' intention, which
would prevent it from being used in practice.
More specifically, for a non-injective |get|
there usually exist many possible |put| functions that can be
combined with it to form a valid BX. For instance, for the same |getHeight|,
the following is a valid |put| too:
< putHeight'' (height, weight) height'
<      = (height', weight x (height' / height))
%< putHeight2 (height, weight) height'
%<      | height==height'  = (height, width)
%<      | otherwise        = (height', 1)
In fact, it is impossible in general to automatically derive
the most suitable valid |put| 
that can be paired with the |get| to form a bidirectional
transformation \cite{CheneyGMS15}.

Since |get| does not contain
sufficient information for a system to automatically
derive intended update policies of |put|,
in order to deal with various update policies of |put| for solving
different problems, significant extensions
to the language for writing |get| are necessary.
One representative problem is \emph{alignment}:
Both the source and view are lists, and the \emph{get} direction is simply a map on lists.
The \emph{put} direction, on the other hand, has a great amount of freedom:
The elements of the view list may be inserted or deleted.
A view deletion can only be reflected as a source deletion, if we want the get direction to be just a map;
for an insertion, however, how do we create a corresponding source element from a usually less informative view element?
The view list may be reordered.
How do we determine which source element should be matched with each view element?
\emph{Matching lenses}~\cite{Barbosa2010} were developed to be able to customize such policies.
There are other finer-grained considerations:
Given an updated view list, how do we decide whether an element is only modified --- so the corresponding source element also only needs modification --- or newly inserted --- so we should delete the corresponding source element and insert a new one?
This requires tracking of how the view list is modified, and frameworks for expressing modification-sensitive update policies were developed~\cite{Diskin:2011,Hofmann2012}.
We may want to go beyond lists to trees and in general any inductive data structures, and, of course, there is work on \emph{generic lenses} to deal with any updates on inductive data structures \cite{Pacheco2012}.
%As a matter of fact, from the original get-based bidirectional
%language \emph{lenses} \cite{Foster2007}, we have seen
%many such extensions, e.g., the \emph{matching lenses}
%to deal with alignment policies \cite{Barbosa2010},
%the \emph{delta lenses} to deal with modification-sensitive update policies
%\cite{Diskin:2011,Hofmann2012}, and the \emph{generic lenses} to deal with
%any updates on inductive data structures \cite{Pacheco2012}.
All these extensions, as seen in the related papers,
are nontrivial, where one has to
rework all the original lens framework by adding new information
to |get| to indirectly control of the behavior of |put|, and to prove
that the extension is sound in the sense that the new |get| and |put|
are well-behaved.

%\TODO{The above is too abstract and not self-contained. The reader won't be able to understand what the alignment problem is, and how it relates to the rectangle example. I think this is related to Prof Hu's question ``What is the old idea we want to explain?''. The old idea is alignment, and we have to explain it instead of just giving references.}

In this paper, we put up
the slogan ``One |put| for All'', in the sense that
a good language for programming |put| can not only
give full control over the behavior of bidirectional transformations,
but also enable us to systematically
develop various domain-specific bidirectional languages and use
them seamlessly in one framework, which
would be nontrivial with the get-based method as seen above.
In the rest of this paper, after a brief review of BiGUL~\cite{Ko2016}, a putback-based
bidirectional language embedded in Haskell, we demonstrate how it can be used to
concisely implement the matching/delta/generic lenses that
are guaranteed to be well-behaved.

%%%
%%% Putback-Based Bidirectional Transformations
%%%
\section{Preparation: Putback-Based BX}

%\TODO{Will revise this part later}

%An under-appreciated fact about well-behaved lenses is that \emph{put} completely determines the behavior of the corresponding \emph{get} --- that is, given a \emph{put} function and two \emph{get} functions each of which forms a well-behaved lens when paired with the \emph{put} function, it must be the case that the two \emph{get} functions are pointwise equal. This fact was already noted by Foster in his PhD thesis~\cite{Foster2009} but had remained neglected until people dug up this idea and started exploring the possibility of specifying BXs in terms of \emph{put} \TODO{citations}.

In this paper, we use BiGUL version 0.9, which is available on Hackage.
Intuitively, think of a BiGUL program of type |BiGUL s v| as describing how to manipulate a state consisting of a source component of type~|s| and a view component of type~|v|; the goal is to copy all information in the view to proper places in the source.
In the simplest case, the view has type~|()| and contains no information, and we can use |Skip :: BiGUL s ()| to leave the source unchanged;
another simple case is when the view has the same type as the source, and we can use |Replace :: BiGUL s s| to replace the entire source with the view.
BiGUL programs compose --- for example, when both the source and the view are pairs, we can use
\begin{spec}
Prod ::  BiGUL s v -> BiGUL s' v' ->
         BiGUL (s, s') (v, v')
\end{spec}
to compose two BiGUL programs on the left and right components respectively; we will typeset the infix application of |Prod| as `|`Prod`|'.
Of course, in most cases the source and view are in more complex forms, and we should somehow transform and decompose them into simpler forms before we can use |Skip|, |Replace|, or |Prod|; this is usually done using two ``rearrangement'' operations on the source and view respectively:
We can use the source rearranging operation
\begin{spec}
$(rearrS [| f |]) :: BiGUL s' v -> BiGUL s v
\end{spec}
where |f| is a ``simple'' $\lambda$-expression of type |s -> s'| for extracting from the source of type~|s| a (usually smaller) source of type~|s'| before performing further updates on the extracted source, or dually the view rearranging operation
\begin{spec}
$(rearrV [| g |]) :: BiGUL s v' -> BiGUL s v
\end{spec}
where the ``simple'' $\lambda$-expression |g| should have type |v -> v'|, and is used to transform the view from type~|v| to type~|v'| before performing further updates.

Most expressiveness of BiGUL comes from its |Case| operation for performing case analysis:
\begin{spec}
Case :: [(s -> v -> Bool, Branch s v)] -> BiGUL s v
\end{spec}
|Case| takes a list of pairs whose first component is a boolean predicate on both the source and the view, and whose second component is a ``branch'', whose type is defined by
\begin{spec}
data Branch s v  =  Normal    (BiGUL s v)
                 |  Adaptive  (s -> v -> s)
\end{spec}
A branch can be a ``normal'' branch, in which case it is a BiGUL program of type |BiGUL s v|, or an ``adaptive'' branch, in which case it is a Haskell function of type |s -> v -> s|.
Roughly speaking, the semantics of |Case| is largely as people would expect: executing the first branch whose associated predicate evaluates to true on the current state, and performing further updates when this branch is normal.
More interestingly, when the chosen branch is adaptive, the source will be replaced by the result of evaluating the associated function on the current state, and the whole |Case| will be executed again.

We introduce some extra notations for writing branches more easily.
The two basic ones are for constructing normal and adaptive branches in general:
\begin{spec}
$(normal    [| p |]) ==> b  = (p, Normal    b)
$(adaptive  [| p |]) ==> f  = (p, Adaptive  f)
\end{spec}
Here the boolean predicate~|p| takes both a source and a view.
Often this predicate is a conjunction of two unary predicates on the source and view respectively, so we introduce another set of notations:
\begin{spec}
$(normalSV    [| pS |] [| pV |]) ==> b
  = ((\s v -> pS s && pV v), Normal    b)
$(adaptiveSV  [| pS |] [| pV |]) ==> f
  = ((\s v -> pS s && pV v), Adaptive  f)
\end{spec}
The unary predicates (|pS| and |pV|) can usually be conveniently expressed as patterns; |normalSV| and |adaptiveSV| can also accept patterns, which should be enclosed in pattern quotation brackets like \([p||\;pat\;||]\).
There are also other variants of |normal| and |adaptive| that are suffixed with only |S| or~|V|, meaning that they accept only one unary predicate on either the source or the view, respectively.

%%%
%%% Positional Alignment
%%%
\section{Positional Alignment}

As a warm-up, let us try to describe in BiGUL the simplest alignment strategy, which matches elements at the same positions in the source and view lists.

Suppose that a research institution has a listing of authors with their
publication count and another listing with its researchers, where authors and
researchers are respectively represented by the following types:
%
\begin{comment}
\begin{code}
type ID = Int
type Name = String
type Publications = Int
\end{code}
\end{comment}
%
\begin{code}
type Author      = (ID, (  Name, Publications))
type Researcher  = (ID,    Name)
\end{code}
%
where |ID :: Int| is the identification number (id for short), |Name :: String|
is the name of the author/researcher, and |Publications :: Int| is the number
of publications of the author. The relation between an author and a researcher
is straightforward: a researcher is an author without the publication count and
thus ids and names of an author must match with the ones of the respective
researcher.
%
This can be expressed using the BiGUL program:
%
\begin{code}
arBX :: BiGUL Author Researcher
arBX = Replace `Prod` $(rearrV   [| \ c -> (c, ()) |])
                                 (Replace `Prod` Skip)
\end{code}
%
First, we want to replace the source id (author) with the view id (researcher)
and thus we use |Replace| on the left-hand side of a |Prod|, whose right-hand
side will deal with the name part. Since there is a mismatch of shape
between the source and the view in that part --- the source is a pair whilst
the view is a single element --- we rearrange the view (researcher name) into a
pair whose second component is an unit. After the rearrangement, we can use a
|Prod| with a |Replace| in the left-hand side to replace the name using a
|Replace| and with a |Skip| on the right-hand side ignoring the value of the
view and keeping the value of the source (publication count) unchanged.

\begin{comment}
The following types for
source (|Source|) and view (|View|) are used as a concrete running example:
%
\begin{code}
type Source  = (Int, (Char, Int))
type View    = (Int, Char)
\end{code}
%
The first |Int| component of the pair should match the first |Int| component of the view,
and the |Char| component of the source should match the |Char|
component of the view.
\TODO{This is abstract. Can we make a concrete story giving the fields meanings, like saying the first |Int| is an id number, the second |Char| is a name, etc?}
This relation between source and view can be expressed
with the following BiGUL program:
%
\begin{code}
myBX :: BiGUL Source View
myBX = Replace `Prod` $(rearrV   [| \ c -> (c, ()) |])
                                 (Replace `Prod` Skip)
\end{code}
\TODO{This is our first BiGUL program, and we should proceed more gently. Something along the line of ``The first thing we want to do is to replace the source id with the view id, so we write |Replace| on the left-hand side of a |Prod|, whose right-hand side will deal with the name part. For that part, there is a mismatch of shape between the source and view, however: The source is a pair, whereas the view is a single element. To make them match (so we can use |Prod|), one way is to rearrange the view into a pair whose second component is a unit. After the rearrangement, we can now use |Prod|, whose left-hand side is a |Replace|, to replace the name, and right-hand side is a |Skip|, keeping \ldots\ unchanged.''}
\end{comment}

The listings are represented by lists of the above types. So we have a list of
authors and a list of researchers. With positional alignment, the relation
between the two lists is simple: each element of the author list matches the
element of researcher list at the same position. When performing any operation
on the view (list of researchers), reordering of the elements (i.e., an element moved to another position) is not taken into
account, and elements are added or deleted at the end of the source.
Just as
with any other programming practice, the BiGUL program must take into account
the several possibilities of source and view values in the update process. For
that, we specify a function (|arMapL|) to map positionally a list of researchers
with a list of authors:
%
\begin{itemize}
  \item both source and view are empty, and we just
    |Skip|;
  \item all elements of the view were processed, so we adapt the source (explained below) by removing
    the extra elements:
    |\ _ _ -> []|;
    \item both source and view have elements, so we update with the head of both
    source and view, and then recurse on the tail of the list:
    |arBX `Prod` arMapL|;
  \item the source does not have enough elements and we create a new one,
    setting to 0 the number of publications of the new author:
    |\ _ ((k,v1) : _) -> [(k,(v1,0))]|.
\end{itemize}
%
These possibilities are packed into a |Case| statement which selects the correct
action for each situation:
%
\begin{code}
arMapL :: BiGUL [Author] [Researcher]
arMapL = Case
  [ $(normalSV [p| [] |] [p| [] |])
      ==> $(rearrV [| \ [] -> () |]) Skip
  , $(adaptiveV [p| [] |])
      ==> \ _ _ -> []
  , $(normalSV [p| (_ : _) |] [p| (_ : _) |])
      ==> $(rearrV [| \ (v:vs) -> (v, vs) |])$
        $(rearrS [| \ (s:ss) -> (s, ss) |])$
          arBX `Prod` arMapL
  , $(adaptiveV [p| (_ : _) |])
      ==> \ _ ((k,v1) : _) -> [(k,(v1,0))]
  ]
\end{code}
%%\begin{code}
%%myMapL :: BiGUL [Source] [View]
%%myMapL = [bcase|
%%  Normal [] [] -> skip
%%  Adaptive _ [] -> \ _ _ -> []
%%  Normal (_ : _) (_ : _) -> update
%%  Adaptive _ (_ : _) -> \ _ ((k,v1) : _) -> [(k,(v1,0))] |]
%%  where  skip = $(rearrV [| \ [] -> () |]) Skip
%%         update = $(rearrV [| \ (v:vs) -> (v, vs) |])$
%%           $(rearrS [| \ (s:ss) -> (s, ss) |])$
%%             myBX `Prod` myMapL
%%\end{code}

When both source and view are empty, or both have elements, a BiGUL program can
be applied: When both are empty, the empty list is produced;
when both have elements, the head of the source is updated with the head of the
view, and then recursion is performed.

In the other two cases, adaptation of the source is required. The first one is
when the view is empty, and the source is modified to be the empty list. After
this adaption, the |Case| statement looks for a normal branch to apply, entering
in the one where both source and view are empty. The second case is when the
view still has elements, but the source is empty. In this case, a new source
element is created from the source element at the head of the list. Then, the
|Case| statement looks for a normal branch, entering in the one where both
source and view have elements, updating the heads and recursing.

To demonstrate the BX functions, let
\begin{code}
source = [(0,("A.",3)),(1,("B.",5)),(2,("C.",8))]
\end{code}
%
Running the |get| function on |source| with the |arMapL| BiGUL program, we obtain the following
result:
%
\begin{lstlisting}
@@>@@ get arMapL source
[(0,"A."),(1,"B."),(2,"C.")]
\end{lstlisting}
%
Now, if we want to expand the last name of the authors/researchers, we just
modify the result above and then put it back into the original source:
%
\begin{lstlisting}
@@>@@@@\hspace{1ex}@@put arMapL source [(0,"Ana"),(1,"Bob"),(2,"Carl")]
[(0,("Ana",3)),(1,("Bob",5)),(2,("Carl",8))]
\end{lstlisting}
%
We can see that the original authors are updated according the changes made to
the view.
However, we can see the limitations of positional update when removing an
element, e.g., \lstinline!(1,"B.")!:
%
\begin{lstlisting}
@@>@@ put arMapL source [(0,"A."),(2,"C.")]
[(0,("A.",3)),(2,("C.",5))]
\end{lstlisting}
%
or adding a new one, e.g., \lstinline!(3,"D.")! before the end%
\footnote{The symbol \lstcontinueline{} denotes line continuation.}:
%
\begin{lstlisting}[breaklines=false]
@@>@@ put arMapL source @@\lstcontinueline@@
    [(0,"A."),(1,"B."),(3,"D."),(2,"C.")]
[(0,("A.",3)),(1,("B.",5)),(3,("D.",8)),(2,("C.",0))]
\end{lstlisting}
%
{\lstset{breakatwhitespace}
Notice the number of publications. For the removal example, it is as
\lstinline!(2,"C.")! was removed and \lstinline!(1,"B.")! was modified to
\lstinline!(2,"C.")!.  For the addition example it is as \lstinline!(2,"C.")!
was added at the end of the view, and \lstinline!(2,"C.")! from the original
view was modified to \lstinline!(3,"D.")!.
}

The |arMapL| program can be generalized to work on lists with arbitrary values.
For that, it must be parametrized with a \emph{create} function, to produce a
source element from a view one as in the fourth branch of the |arMapL| |Case|,
and with a BiGUL program to be run on the elements instead of |arBX|:
\begin{code}
mapL :: (v -> s) -> BiGUL s v -> BiGUL [s] [v]
\end{code}
%
\begin{comment}
\begin{code}
mapL c u = Case
  [ $(normalSV [p| [] |] [p| [] |])$ $(rearrV [| \ [] -> () |]) Skip
  , $(adaptiveV [p| [] |])$ \ _ _ -> []
  , $(normalSV [p| (_ : _) |] [p| (_ : _) |])$
      $(rearrV [| \ (v:vs) -> (v, vs) |])$
        $(rearrS [| \ (s:ss) -> (s, ss) |])$
          u `Prod` mapL c u
  , $(adaptiveV [p| (_ : _) |])$ \ _ (v : _) -> [c v]
  ]
\end{code}
\end{comment}

%%%
%%% Key-Based Alignment
%%%
\section{Key-Based Alignment}

The positional alignment strategy is not the best regarding our example
shown in the previous section. Looking at the types, we can define a better
strategy using the ids to match the authors and researchers as it is done
naturally in other contexts.

More complex alignment strategies can be implemented using BiGUL. One example is
a key-based one, where elements of the source and the view are paired based on a
key component from each of the elements.
Thus, we can use this strategy to implement a better alignment.

One could implement a key-based alignment strategy using a structure similar to
the positional alignment. However, a simpler approach is available.
The idea to implement this strategy is to separate the program in two parts:
%
\begin{itemize}
  \item alignment of the elements;
  \item the actual update, using a positional mapping which is sufficient when
  the elements are aligned.
\end{itemize}

To align the elements, we must first be able to extract a key from source and
view elements. For our running example, we use the first component of the
source, and the same for the view. Thus, we can use the |fst| function to
extract the key from either elements. In order to help with the implementation,
we define a function to check if the source and the view are aligned:
%
\begin{code}
isAligned s v =  length s == length v
                 && and (zipWith kmatch s v)
  where kmatch se ve = fst se == fst ve
\end{code}
%
We consider that source and view are aligned if both have the same number of
elements, and that the keys match element-wise.

In the case that the two lists are not aligned, we define a function that adapts a
source such that when applied they become aligned. This is performed by traversing the
view and fetching the first corresponding element in the original source. If
such element is not present, we create it. At the end, source elements not
present in view are discarded. The adaptation of the source can be implemented
as:
%
\begin{code}
arKeyMatchAdapt s v = Prelude.map getSourceElement v
  where  getSourceElement ve =
           case Prelude.filter ((== fst ve) . fst) s of
             []        -> create ve
             (se : _ ) -> se
         create (k, v1) = (k, (v1, 0))
\end{code}

When the source and the view are aligned, a simple positional update, as defined
in the previous section, can be used. Thus, putting it all together, we obtain
the following BiGUL program:
%
\begin{code}
arKeyMatch ::  BiGUL [Author] [Researcher]
arKeyMatch = Case
  [ $(normal [| isAligned |]) ==> arMapL
  , $(adaptive [| \ _ _ -> True |]) ==> arKeyMatchAdapt ]
\end{code}

The result of running the |get| function with |arKeyMatch| is the same as with
|arMapL| since they only differ in the alignment strategy:
%
\begin{lstlisting}
@@>@@ source
[(0,("A.",3)),(1,("B.",5)),(2,("C.",8))]
@@>@@ get arKeyMatch source
[(0,"A."),(1,"B."),(2,"C.")]
\end{lstlisting}
%
Running the |put| function also has the same result when the elements are the
same and the order did not change:
%
\begin{lstlisting}
@@>@@ put arKeyMatch source @@\lstcontinueline@@
    [(0,"Ana"),(1,"Bob"),(2,"Carl")]
[(0,("Ana",3)),(1,("Bob",5)),(2,("Carl",8))]
\end{lstlisting}
%
However, when removing elements, e.g., \lstinline!(1,"B.")! or adding new ones,
e.g., \lstinline!(3,"D.")!, key-based alignment is more precise than positional:
%
\begin{lstlisting}
@@>@@ put arKeyMatch source [(0,"A."),(2,"C.")]
[(0,("A.",3)),(2,("C.",8))]
@@>@@ put arKeyMatch source @@\lstcontinueline@@
    [(0,"A."),(1,"B."),(3,"D."),(2,"C.")]
[(0,("A.",3)),(1,("B.",5)),(3,("D.",0)), @@\lstcontinueline@@
  (2,("C.",8))]
\end{lstlisting}
%
Nonetheless, key-based alignment also has its limitations, e.g., when modifying
the key of an element (\lstinline!(1,"B.")! to \lstinline!(4,"B.")!):
%
\begin{lstlisting}
@@>@@ put arKeyMatch source@@\hspace{1ex}@@[(0,"A."),(4,"B."),(2,"C.")]
[(0,("A.",3)),(4,("B.",0)),(2,("C.",8))]
\end{lstlisting}

As with the positional update, this program can be generalized for key-based
alignment on lists with arbitrary contents. For that, the |arKeyMatch| function
must be parametrized with a function to get a key component from the source, another
function to get the key component from the view, and the create function and BiGUL update
program as with |mapL|:
%
\begin{spec}
keyMatch  :: Eq k => (s -> k) -> (b -> k)
          -> (v -> s) -> BiGUL s v -> BiGUL [s] [v]
\end{spec}

%%%
%%% Delta-Based List Alignment
%%%
\section{Delta-Based List Alignment}

The pattern used for the implementation of the key-based alignment strategy ---
the separation of the alignment of source and view in a step and then the
element-wise update in another one --- is actually very powerful and allows to
implement much more complex alignment strategies.

{\lstset{prebreak={},breakatwhitespace=true}
For instance, going back to the running example, if one wants to change the id
of a researcher alongside with other operations, that would not be possible with
either the positional nor the key-based alignment strategies. More concretely,
putting back \lstinline![(0,"A."),(1,"C.")]!, where \lstinline!(1,"B.")! was
removed and \lstinline!(2,"C.")! was changed to \lstinline!(1,"C.")!, into
\lstinline![(0,("A.",3)),(1,("B."),5),(2,("C.",8))]!
would not yield the expected
\lstinline![(0,("A.",3)),(1,("C.",8))]!. In this case, we are missing
information about the operations performed which would lead to a correct update
of the list of authors.
}

Alignment can be made more precise using information about how the view is modified.
If we extract the relation of elements in the original
view to the elements in the modified view, then the alignment performed when
updating the source can be completely correct.

The relation of elements in the original view with the ones in the modified view
can be defined by a mapping from the location of the element in the original
artifact to the location of the element in the modified artifact.
The location
can be defined as an integer index within the container
%
\begin{code}
type Loc = Int
\end{code}
%
and the mapping, i.e., the delta, can be defined as a set of pairs of these
locations
%
\begin{code}
type Delta = Set (Loc, Loc)
\end{code}

Furthermore, we need a method to determine from a delta if some artifact has
undergone any positional change (movement within the container, addition, or
removal), which can be accomplished by checking if all elements are in the delta
and that each location in the delta is related to the same location:
%
\begin{spec}
delta == getId artifact
\end{spec}
%
The |getId| function creates an identity delta based on the locations of the
artifact:
%
\begin{code}
getIdL :: [a] -> Delta
getIdL = Set.map (\ l -> (l, l)) . locs
\end{code}

%%% Delta Alignment for Lists
\subsection{Delta Alignment for Lists}

In order to implement such kind of alignment in BiGUL, the delta can be inserted
into the source, since we can manipulate it using adaptation in
|Case| branches.

The implementation of delta-based alignment is similar to the key-based one:
%
\begin{enumerate}
  \item modification of the source aligning to the view using a delta;
  \item a positional update.
\end{enumerate}
%
However, the delta in the source introduces a bit more complexity to deal with the
additional information. We no longer use the keys of the elements to check if
the lists are aligned, but we verify that purely based on the delta: If the
identity delta of the source and the identity delta of the view are both equal
to the given delta, then both source and view elements are aligned:
%
\begin{code}
isDeltaAlignedL (s,d) v = d == getIdL v && d == getIdL s
\end{code}
%
When the source and the view are not aligned, we adapt the source similarly to
the key-based alignment. However, in this case we also have the delta present in
the source, which should be the same as both the source and the view after the
adaptation so that we can perform the positional mapping.
%
Implementing this in the running example:
%
\begin{code}
arAlignL'  ::  BiGUL ([Author], Delta) [Researcher]
arAlignL' = Case
  [ $(normal [| isDeltaAlignedL |])
      ==> $(rearrS [| \(s, _) -> s |]) arMapL
  , $(adaptiveS [| const True |])
      ==> \(s,d) v ->  let s' = arAdaptDeltaL s v d
                       in (s', getIdL v) ]
\end{code}
%
An alternative |Case| statement is used to check which of these two steps are to
be performed. This is done based on the changes performed on the view: if no
changes were performed, the delta maps each element's position to the same
position, i.e., the identity delta. However, the delta being the same as |getIdL
v| does not mean that no changes were performed to the view, e.g., some values
were deleted, thus not present in the view nor in the delta relation. To
deal with this situation, we ensure that the delta is also equal to the identity delta of
the source, i.e., both source and view contain the same positions and the update
can be safely performed.
Otherwise, a
transformation is performed on the source to rearrange the elements based on the
delta, create missing view elements, and
delete no longer existent view elements:
%
\begin{code}
arAdaptDeltaL  :: [Author] -> [Researcher] -> Delta
               -> [Author]
arAdaptDeltaL s v d =
  Prelude.map idOrCreate (Set.elems $ locs v)
  where  idOrCreate i =  let  js = rngOf i d
                         in  if js /= Set.empty
                             then s !! Set.findMin js
                             else  let (k, v1) = v !! i
                                   in (k, (v1, 0))
\end{code}
%
%Note that in |alignL'| the create function |c| given to |mapL| is not required since
%|adaptDeltaL| creates the missing elements.

However, having the delta paired with the source might be inconvenient. To deal with
such situation, a wrapper is made that takes care of dealing with the delta:
%
\begin{code}
arAlignL :: Delta -> BiGUL [Author] [Researcher]
arAlignL d = emb g p
  where  g s    = get arAlignL' (s, getIdL s)
         p s v  = fst $ put arAlignL' (s, d) v
\end{code}
%
This wrapper implements directly the |get| and |put| functions (respectively |g|
and |p|), and
embeds them into a BiGUL program, since this pair of |get|/|put| functions is
well-behaved:\\
%
\textsc{GetPut} -- this law states that if no changes to the view are performed,
then putting it back into the source does not alter the source. Since no changes
are performed, the delta is the identity delta of the view, i.e., |delta =
getIdL v| where |v = g s|. Furthermore, |v| is consistent with |(s, getIdL s)|,
so we know that |getIdL s = getIdL v|. Applying |fst| to both sides of the
following equation gives us |GetPut|:
%
\begin{spec}
put arAlignL' (s, getIdL v) (get arAlignL' (s, getIdL s))
== { getIdL v == getIdL s }
put arAlignL' (s, getIdL s) (get arAlignL' (s, getIdL s))
== { GetPut for arAlignL' }
(s, getIdL s)
\end{spec}
%
\textsc{PutGet} -- this law states that the view after updating a source is the
same as the one used for the update. As the result of the |put| function, let
|(s', delta1) = put arAlignL' (s, delta) v|, thus |(s', delta1)| is consistent
with |v| and |delta1 == getIdL s'|. Applying the |get| function~|g|:
%
\begin{spec}
get arAlignL' (s', getIdl s')
== { delta1 = getIdL s' }
get arAlignL' (s', delta1)
== { let binding }
get arAlignL' (put arAlignL' (s, delta))
== { PutGet for arAlignL' }
v
\end{spec}

As an aside, the embedding of |get| and |put| functions can be defined as a BiGUL program:
%
\begin{code}
emb :: Eq v => (s -> v) -> (s -> v -> s) -> BiGUL s v
emb g p = Case
  [ $(normal [| \x y -> g x == y |])$
      $(rearrV [| \x -> ((), x) |])$
        Dep Skip (\x () -> g x)
  , $(adaptive [| \_ _ -> True |]) p ]
\end{code}
%
Here what the normal branch does is, roughly speaking, leaving the source~|x| as it is while ignoring the view, since we know that the view is necessarily |g x|.
In order for an embedding to be well-behaved, running the |put| function should
produce a source that when running |get| should return the view given to the
former, as stated by the \textsc{GetPut} law and enforced by the case structure.
Furthermore, the view should be completely defined by the source.
It is interesting to note that the two-branch structure of |emb| is comparable with that of |arAlignL'|:
The normal branch of |arAlignL'| deals with the case where the source and view are roughly consistent, i.e., aligned, but the elements are not yet completely synchronized pairwise; otherwise, when the source and view are too inconsistent, i.e., not aligned, the adaptive branch comes in and restores enough consistency such that the normal branch can take over.
The normal branch of |emb|, on the other hand, applies when the source and view are fully consistent (as specified by~|g|), and its adaptive branch restores full consistency (by~|p|) when encountering inconsistent pairs of source and view.
In short, |emb| is an extreme instance of the two-branch structure.


To run the delta alignment, we thus need to provide a delta to the BiGUL
program. With the running example, we can use the following deltas:
%
\begin{code}
d1, d2, d3 :: Delta
d1 = fromList [(0,0),(1,1),(2,2)]
d2 = fromList [(0,0),(1,2),(2,1)]
d3 = fromList [(0,0),(1,1)]
\end{code}
%
For the \emph{get} direction, the delta is ignored, and the result is the same
as for the previous kinds of alignment:
%
\begin{lstlisting}
@@>@@ source
[(0,("A.",3)),(1,("B.",5)),(2,("C.",8))]
@@>@@ get (arAlignL @@|d1|@@) source
[(0,"A."),(1,"B."),(2,"C.")]
\end{lstlisting}
%
However, in the put direction, results may vary depending on the given delta,
e.g., no changes are performed (using |d1|):
%
\begin{lstlisting}
@@>@@ put (arAlignL @@|d1|@@) source @@\lstcontinueline@@
    [(0,"A."),(1,"B."),(2,"C.")]
[(0,("A.",3)),(1,("B.",5)),(2,("C.",8))]
\end{lstlisting}
%
versus a swap between the last two elements (using |d2|):
%
\begin{lstlisting}
@@>@@ put (arAlignL @@|d2|@@) source @@\lstcontinueline@@
    [(0,"A."),(1,"B."),(2,"C.")]
[(0,("A.",3)),(1,("B.",8)),(2,("C.",5))]
\end{lstlisting}
%
Note that the elements were not swapped in the view, but the delta |d2|
indicates that the elements were swapped. This is equivalent to swapping those
elements and modifying the values to the ones at the same position in the
original view.
%
A similar situation occurs when the view is not modified, but one element is not
in the delta:
%
\begin{lstlisting}
@@>@@ put (arAlignL @@|d3|@@) source @@\lstcontinueline@@
    [(0,"A."),(1,"B."),(2,"C.")]
[(0,("A.",3)),(1,("B.",5)),(2,("C.",0))]
\end{lstlisting}
%
In this case, it is equivalent to remove the last element and inserting it
again.

The delta alignment implementation can be generalized for arbitrary list
contents, resulting in the following equivalent functions with additional
parameters for the create function and BiGUL update program to apply to the
elements:
%
\begin{spec}
adaptDeltaL :: (v -> s) -> [s] -> [v] -> Delta -> [s]
alignL'  ::  BiGUL s v -> (v -> s)
         ->  BiGUL ([s], Delta) [v]
alignL  :: Eq v => BiGUL s v -> (v -> s) -> Delta
        -> BiGUL [s] [v]
\end{spec}
\begin{comment}
\begin{code}
alignL'  ::  BiGUL s v -> (v -> s)
         ->  BiGUL ([s], Delta) [v]
alignL' b c = Case
  [ $(normal [| \(s, d) v  -> d == getIdL v
                           && d == getIdL s |])
      ==> $(rearrS [| \(s, _) -> s |]) (mapL c b)
  , $(adaptiveS [| const True |])
      ==> \(s,d) v ->  let s' = adaptDeltaL c s v d
                       in (s', getIdL v) ]

adaptDeltaL :: (v -> s) -> [s] -> [v] -> Delta -> [s]
adaptDeltaL c s v d = Prelude.map idOrCreate (Set.elems $ locs v)
  where  idOrCreate i =  let js = rngOf i d
                         in  if js /= Set.empty
                             then data_ s !! Set.findMin js
                             else c (data_ v !! i)

alignL  :: Eq v
        => BiGUL s v -> (v -> s) -> Delta
        -> BiGUL [s] [v]
alignL b c d = emb g p
  where  g s    = get (alignL' b c) (s, getIdL s)
         p s v  = fst $ put (alignL' b c) (s, d) v
\end{code}
\end{comment}



%%%
%%% Delta-Based Tree Alignment
%%%
\section{Delta-Based Tree Alignment}

Lists are not the only structures capable of storing information, nor the only
ones that are used in bidirectional transformation applications. However, other
containers bring new challenges and we need to take them into account, e.g.,
the shape of the container.
One such container where delta alignment can be implemented is the tree. Many kinds
of trees exist, but we use a binary tree with labels in the nodes:
%
\begin{code}
data Tree a = Nil | Node a (Tree a) (Tree a)
  deriving (Show, Functor)
\end{code}
\begin{comment}
\begin{code}
instance Eq a => Eq (Tree a) where
  (==) Nil Nil = True
  (==) (Node a al ar) (Node b bl br) = a == b && al == bl && ar == br
  (==) _ _ = False

instance Generic (Tree a) where
      type Rep (Tree a) = (:+:) U1 ((:*:) (K1 R a) ((:*:) (K1 R (Tree a)) (K1 R (Tree a))))
      from Nil = L1 U1
      from (Node var_arJr var_arJs var_arJt)
        = R1 ((:*:) (K1 var_arJr) ((:*:) (K1 var_arJs) (K1 var_arJt)))
      to (L1 U1) = Nil
      to (R1 ((:*:) (K1 var_arJr) ((:*:) (K1 var_arJs) (K1 var_arJt))))
        = Node var_arJr var_arJs var_arJt
$(return [])

instance Shapely Tree where
    traverse f = (hinn >< id) . traverse f . (hout >< id)
type instance HF Tree = HConst One :+~: HParam :*~: (HId :*~: HId)
instance Hu Tree where
    hout Nil = InlF $ ConsF _L
    hout (Node x l r) = InrF $ ProdF (IdF x) (ProdF l r)
    hinn (InlF (ConsF _)) = Nil
    hinn (InrF (ProdF (IdF x) (ProdF l r))) = Node x l r
instance FMonoid Tree where
    fzero = Nil
    fplus t Nil = t
    fplus t (Node x l r) = Node x (fplus t l) r
\end{code}
\end{comment}

Tree elements can also be indexed by locations. The position of tree elements
can be established linearly in an in-order fashion:
%
\begin{code}
locsT :: Tree a -> Tree Loc
locsT = fst . aux 0
  where  aux i0 Nil = (Nil, i0)
         aux i0 (Node _ l0 r0) =
           let  (l,i1  ) = aux i0 l0
                (r,i   ) = aux (i1+1) r0
           in (Node i1 l r, i)

flattenT :: Tree a -> [a]
flattenT Nil = []
flattenT (Node a l r) = flattenT l ++ [a] ++ flattenT r
\end{code}
%
Thus the |Delta| type used for lists can also be used for trees, and the
identity delta can be obtained with the function |getIdT :: Tree a -> Delta|.
%
\begin{comment}
\begin{code}
getIdT :: Tree a -> Delta
getIdT = Set.map (\ l -> (l, l)) . locs
\end{code}
\end{comment}

The approach to implement the delta-based alignment for trees is similar to the
approach used in the other implementations:
%
\begin{enumerate}
  \item modification of the source aligning to the view using a delta;
  \item a positional update.
\end{enumerate}

The adaptation function for tree can be
%
\begin{code}
arAdaptDeltaT  :: Tree Author -> Tree Researcher
               -> Delta -> Tree Author
arAdaptDeltaT s v d = Prelude.fmap idOrCreate (locsT v)
  where  idOrCreate i =
           let js = rngOf i d
           in  if js /= Set.empty
               then flattenT s !! Set.findMin js
               else  let (k, v1) = flattenT v !! i
                     in (k, (v1, 0))
\end{code}
%
where we take advantage of the |fmap| function, deriving from the fact that |Tree| is a
functor.
This adaptation does two important tasks: it molds the source tree in order to
match the shape of the view one; and, it aligns the elements in order to perform
a positional update.

The implementation of the positional tree update is similar to the one for
lists, since both have only two data constructors. However, trees have double
recursion which must be taken into account.
%
\begin{code}
arMapT :: BiGUL (Tree Author) (Tree Researcher)
arMapT = Case
  [ $(normalSV [p| Nil |] [p| Nil |])
      ==> $(rearrV [| \ Nil -> () |]) Skip
  , $(adaptiveV [p| Nil |])
      ==> \ _ _ -> Nil
  , $(normalSV [p| Node _ _ _ |] [p| Node _ _ _ |])
      ==>  $(rearrV  [| \ (Node v vl vr)
                       -> (v, (vl, vr)) |]) $
             $(rearrS  [| \ (Node s sl sr)
                         -> (s, (sl, sr)) |])$
                  arBX `Prod` (arMapT `Prod` arMapT)
  , $(adaptiveV [p| (Node _ _ _) |])
      ==> \ _ (Node (k, v1) _ _) -> Node  (k, (v1, 0))
                                          Nil    Nil
  ]
\end{code}

Before implementing the delta-based alignment for trees, we must revisit the
function to check if the source and the view are aligned. For the list case, the
shape is isomorphic to naturals and thus we have the shape of a list equal to
its length. This aspect is taken into account when verifying the identity delta
of the list with the given delta. However, for trees this is different and we
thus need to include another condition:
%
\begin{code}
isDeltaAlignedT (s,d) v  =   d == getIdT v
                         &&  d == getIdT s
                         &&  locsT s == locsT v
\end{code}
%
Comparing the positions of the source tree and the view one we ensure that both
have the same shape.

At this point, we can define a delta-based
alignment for trees in a similar way as with lists:
%
\begin{code}
arAlignT'
  :: BiGUL (Tree Author, Delta) (Tree Researcher)
arAlignT' = Case
  [ $(normal [| isDeltaAlignedT |])
      ==> $(rearrS [| \(s, _) -> s |]) arMapT
  , $(adaptiveS [| const True |])
      ==> \(s,d) v ->  let s' = arAdaptDeltaT s v d
                       in (s', getIdT v) ]
\end{code}
%
and corresponding wrapper:
%
\begin{code}
arAlignT  :: Delta
          -> BiGUL (Tree Author) (Tree Researcher)
arAlignT d = emb g p
  where  g s    = get arAlignT' (s, getIdT s)
         p s v  = fst $ put arAlignT' (s, d) v
\end{code}

The application of |get| and |put| to trees is similar to the application of
them to lists. The |get| functions takes the source tree and produces a view
tree where its elements are the view of their correspondence in the source:
%
\begin{lstlisting}
@@>@@ get (arAlignT @@|d1|@@) (Node (1,("B.",5)) @@\lstcontinueline@@
      (Node (0,("A.",3)) Nil Nil) @@\lstcontinueline@@
      (Node (2,("C.",8)) Nil Nil))
Node (1,"B.")  (Node (0,"A.") Nil Nil) @@\lstcontinueline@@
               (Node (2,"C.") Nil Nil)
\end{lstlisting}
%
The delta specification in the |put| transformation is the same as with lists:
%
\begin{lstlisting}
@@>@@ put (arAlignT @@|d1|@@) @@\lstcontinueline@@
    (Node (1,("B.",5)) @@\lstcontinueline@@
      (Node (0,("A.",3)) Nil Nil) @@\lstcontinueline@@
      (Node (2,("C.",8)) Nil Nil)) @@\lstcontinueline@@
    (Node (1,"B.") @@\lstcontinueline@@
      (Node (0,"A.") Nil Nil) @@\lstcontinueline@@
      (Node (2,"C.") Nil Nil))
Node (1,("B",5))  (Node (0,("A.",3)) Nil Nil) @@\lstcontinueline@@
                  (Node (2,("C.",8)) Nil Nil)
\end{lstlisting}
%
We can also change the shape of a tree in the view:
%
\begin{lstlisting}
@@>@@ put (arAlignT @@|d1|@@) @@\lstcontinueline@@
    (Node (1,("B.",5)) @@\lstcontinueline@@
      (Node (0,("A.",3)) Nil Nil) @@\lstcontinueline@@
      (Node (2,("C.",8)) Nil Nil)) @@\lstcontinueline@@
    (Node (0,"A.") Nil @@\lstcontinueline@@
      (Node (1,"B.") Nil @@\lstcontinueline@@
        (Node (2,"C.") Nil Nil)))
Node (0,"A.",3) Nil @@\lstcontinueline@@
  (Node (1,"B.",5) Nil @@\lstcontinueline@@
    (Node (2,"C.",8) Nil Nil))
\end{lstlisting}

The delta alignment implementation can be generalized for arbitrary tree
contents, with the following equivalent functions. Similarly to the list
version, the functions are parametrized with a \emph{create} function and a
BiGUL program to apply to the specific elements.
%
\begin{spec}
mapT  :: (v -> s) -> BiGUL s v
      -> BiGUL (Tree s) (Tree v)
adaptDeltaT  :: (v -> s) -> Tree s -> Tree v -> Delta
             -> Tree s
alignT'  ::  BiGUL a b -> (b -> a)
         ->  BiGUL (Tree a, Delta) (Tree b)
alignT  :: Eq v => BiGUL s v -> (v -> s) -> Delta
        -> BiGUL (Tree s) (Tree v)
\end{spec}
%
\begin{comment}
\begin{code}
adaptDeltaT  :: (v -> s) -> Tree s -> Tree v -> Delta
             -> Tree s
adaptDeltaT c s v d = Prelude.fmap idOrCreate (locsT v)
  where  idOrCreate i =  let js = rngOf i d
                         in  if js /= Set.empty
                             then data_ s !! Set.findMin js
                             else c (data_ v !! i)

mapT  :: (v -> s) -> BiGUL s v
      -> BiGUL (Tree s) (Tree v)
mapT c u = Case
  [ $(normalSV [p| Nil |] [p| Nil |])
      ==> $(rearrV [| \ Nil -> () |]) Skip
  , $(adaptiveV [p| Nil |])
      ==> \ _ _ -> Nil
  , $(normalSV [p| Node _ _ _ |] [p| Node _ _ _ |])
      ==>  $(rearrV  [| \ (Node v vl vr)
                       -> (v, (vl, vr)) |]) $
             $(rearrS  [| \ (Node s sl sr)
                         -> (s, (sl, sr)) |])$
                  u `Prod` (mapT c u `Prod` mapT c u)
  , $(adaptiveV [p| (Node _ _ _) |])
      ==> \ _ (Node v _ _) -> Node (c v) Nil Nil
  ]

alignT'  ::  BiGUL a b -> (b -> a)
         ->  BiGUL (Tree a, Delta) (Tree b)
alignT' b c = Case
  [ $(normal [| \(s, d) v  ->  d == getIdT v
                           &&  d == getIdT s |])
      ==> $(rearrS [| \(s, _) -> s |]) (mapT c b)
  , $(adaptiveS [| const True |])
      ==> \(s,d) v ->  let s' = adaptDeltaT c s v d
                       in (s', getIdT v) ]

alignT  :: Eq v
        => BiGUL s v -> (v -> s) -> Delta
        -> BiGUL (Tree s) (Tree v)
alignT b c d = emb g p
  where  g s    = get (alignT' b c) (s, getIdT s)
         p s v  = fst $ put (alignT' b c) (s, d) v
\end{code}
\end{comment}

%%%
%%% Generic Delta-Based Alignment
%%%
\section{Generic Delta-Based Alignment}

We have explained how to do delta-based alignment for lists and then for trees,
and these experiences actually make us sufficiently prepared to go generic!
In this final installment, we show that delta-based alignment can be generically implemented for any other containers.
%The
%implementations for the list and tree cases are generalizable to other
%containers.

%%% Containers as Shape and Data
\subsection{Containers as Shape and Data}

\citet{Pacheco2012} rely on types with explicit notion of shape and data in
their delta-alignment over inductive types, a
property provided by polymorphic data types in functional programming.
Moreover, they apply a notation from \emph{shapely types}~\cite{jay1995} in
order to have tools to work with these data types.
Employing these concepts, one can abstract from the shapes of both source and
view, and just take the data into account for the alignment process.

Thus, a polymorphic type \(T~a\) can be characterized by three functions:
|shape :: T a -> T ()| to extract the shape;
|data_ :: T a -> [a]| to extract the data;
and, |recover :: (T (), [a]) -> T a| to rebuild the type value
from its shape and data.
For a list of researchers \lstinline!l = [(0,"A."),(1,"B."),(2,"C.")]! we have:
%
\begin{lstlisting}
@@>@@ shape l
[(),(),()]
@@>@@ data_ l
[(0,"A."),(1,"B."),(2,"C.")]
@@>@@ recover (shape l, data_ l)
[(0,"A."),(1,"B."),(2,"C.")]
\end{lstlisting}
%
{\lstset{prebreak={}}
and for a tree of researchers \lstinline!t = Node (1,"B.") (Node (0,"A.") Nil Nil) (Node (2,"C.") Nil Nil)!:
}
%
\begin{lstlisting}
@@>@@ shape t
Node () (Node () Nil Nil) (Node () Nil Nil)
@@>@@ data_ t
[(0,"A."),(1,"B."),(2,"C.")]
@@>@@ recover (shape t, data_ t)
Node (1,"B.") (Node (0,"A.") Nil Nil) @@\lstcontinueline@@
              (Node (2,"C.") Nil Nil)
\end{lstlisting}
%
For flexibility, these functions are defined in a type class
%
\begin{spec}
class Shapely (t :: * -> *) where
  shape :: t a -> t ()
  data_ :: t a -> [a]
  recover :: (t (), [a]) -> t a
\end{spec}

On top of these functions, it is possible to define new ones, e.g., |locs ::
T a -> Set Loc| to get all the locations of the data elements within the
container.

%%% Positional Mapping
\subsection{Positional Mapping}

The positional update is one of the aspects that is specific to each data type.
To solve this issue in a simple manner, we introduce a new type class
%
\begin{code}
class Shapely t => Positional t where
  positionalMap  :: (v -> s) -> BiGUL s v
                 -> BiGUL (t s) (t v)
\end{code}
%
\begin{comment}
\begin{code}
instance Positional [] where
  positionalMap = mapL
instance Positional Tree where
  positionalMap = mapT
\end{code}
\end{comment}
%
where the |positionalMap| function maps a BiGUL program element-wise.
For the list container |positionalMap = mapL|
and for the tree container |positionalMap = mapT|.

%%% Generic Delta Alignment
\subsection{Generic Delta Alignment}

A key component in delta alignment is the position of elements. Having access to
element positions, we can obtain the identity delta:
%
\begin{code}
getId :: Shapely s => s a -> Delta
getId = Set.map (\ l -> (l, l)) . locs
\end{code}

Firstly, we need a generalization of the adaptation process. With lists, we take
the view and then insert the source elements at the correct positions. For
trees, the process is similar: we flatten the source tree extracting its data in
order to insert it into the shape of the view. Working with shapely types, this
is achieved by recovering
a container with the shape of the view, but with the data of the original source
or with created data when new elements were added:
%
\begin{code}
adaptDelta  :: Shapely s
            => (b -> a) -> s a -> s b -> Delta -> s a
adaptDelta c s v d = recover (newShape, newData)
  where  newShape = shape v
         newData = Prelude.map idOrCreate (Set.elems $ locs v)
         idOrCreate i =  let js = rngOf i d
                         in  if js /= Set.empty
                             then data_ s !! Set.findMin js
                             else c (data_ v !! i)
\end{code}
%
With this function, any shapely type can be adapted, including lists and trees.

Another aspect to take into account is to check if the source and view
containers are aligned. With lists we just compare the given delta with the
identity deltas of source and view. With trees, in addition to the conditions
used with lists, we also check the extracted locations. Actually, the extracted
locations contains the shape of the tree, which is what we need in order to
verify that some change was performed to the view in addition to the delta. Thus,
we check if the source and view are aligned with:
%
\begin{code}
isDeltaAligned (s,d) v  =   d == getIdT v
                        &&  d == getIdT s
                        &&  shape s == shape v
\end{code}
%
and use it directly in the alignment function where we perform a positional
update when both source and view are aligned, or we adapt when they are not
aligned:
%
\begin{code}
align'  ::  (Shapely t, Positional t)
        =>  BiGUL s v -> (v -> s)
        ->  BiGUL (t s, Delta) (t v)
align' b c = Case
  [ $(normal [| isDeltaAligned |])
      ==> $(rearrS [| \(s, _) -> s |]) (positionalMap c b)
  , $(adaptiveS [| const True |])
      ==> \(s,d) v ->  let s' = adaptDelta c s v d
                       in (s', getId v) ]
\end{code}
%
\begin{code}
align  :: (Shapely t, Positional t, Eq (t v))
       => BiGUL s v -> (v -> s) -> Delta
       -> BiGUL (t s) (t v)
align b c d = emb g p
  where  g s    = get (align' b c) (s, getId s)
         p s v  = fst $ put (align' b c) (s, d) v
\end{code}

%%% Other Matching Algorithms Built Upon Deltas
\subsection{Other Matching Algorithms Built Upon Deltas}

With the implementation of delta-based alignment, we can implement other
alignment strategies upon the deltas without much work.
It is possible to make minor changes to the |align| function to
implement other kinds of alignments, e.g., key-based:
%
\begin{code}
keyAlign :: (Shapely s, Positional s, Eq (s b), Eq b, Eq k)
  => BiGUL a b -> (b -> a) -> (a -> k) -> (b -> k)
  -> BiGUL (s a) (s b)
keyAlign b c sk vk = emb g p
  where  g s    = get (align' b c) (s, getId s)
         p s v  = fst $ put  (align' b c)
                             (s, keyDelta sk vk s v) v
\end{code}

The |keyAlign| function, instead of receiving the delta, receives two
functions to get the key component of the view and the source, respectively.
Then, using the original source and the modified view, another function is used
to infer a delta:
%
\begin{code}
keyDelta :: (Shapely s, Eq k)
  => (a -> k) -> (b -> k) -> s a -> s b -> Delta
keyDelta sk vk ss vs = Set.fromList [ (sp, vp)  |  (s, sp) <- sps
                                                ,  (v, vp) <- vps
                                                ,  sk s == vk v   ]
  where  sps  = zip (data_ ss) (Set.elems $ locs ss)
         vps  = zip (data_ vs) (Set.elems $ locs vs)
\end{code}

It is then possible to apply key-based alignment on any structure that has an
implementation of delta-based alignment. The same function can be used for,
e.g., lists:
%
\begin{lstlisting}
@@>@@ put (keyAlign arBX arCreate fst fst) @@\lstcontinueline@@
    [(0,("A.",3)),(1,("B.",5)),(2,("C.",8))] @@\lstcontinueline@@
    [(0,"A."),(1,"B."),(2,"C.")]
[(0,("A.",3)),(1,("B.",5)),(2,("C.",8))]
\end{lstlisting}
%
and for trees:
%
\begin{lstlisting}
@@>@@ put (keyAlign arBX arCreate fst fst) @@\lstcontinueline@@
    (Node (1,("B.",5)) @@\lstcontinueline@@
      (Node (0,("A.",3)) Nil Nil) @@\lstcontinueline@@
      (Node (2,("C.",8)) Nil Nil)) @@\lstcontinueline@@
    (Node (1,"B.") @@\lstcontinueline@@
      (Node (0,"A.") Nil Nil) @@\lstcontinueline@@
      (Node (2,"C.") Nil Nil))
Node (1,("B.",5)) (Node (0,("A.",3)) Nil Nil) @@\lstcontinueline@@
                  (Node (2,("C.",8)) Nil Nil)
\end{lstlisting}
%
where |arCreate (k, v1) = (k, (v1, 0))|.
%
\begin{comment}
\begin{code}
arCreate :: Researcher -> Author
arCreate (k, v1) = (k, (v1, 0))
\end{code}
\end{comment}


%%%
%%% Conclusion
%%%
\section{Conclusion}

We hope to send the following two messages through this %pearl
paper. One is that putback-based bidirectional programming is not that 
difficult in BiGUL, a simple but powerful putback-based
language. The other is that a \emph{single} well-designed putback-based
bidirectional programming language can serve as the basis for developing
many useful domain-specific bidirectional languages/libraries.
We have shown that, with BiGUL alone, we can implement various alignment
strategies which previously had to be implemented with separate bidirectional frameworks.
%that allow both get-based and put-based bidirectional programming.

%\appendix
%\section{Appendix Title}
%
%This is the text of the appendix, if you need one.

%\acks
%
%Acknowledgments, if needed.

% We recommend abbrvnat bibliography style.

\bibliographystyle{abbrvnat}
\bibliography{references}

%% The bibliography should be embedded for final submission.
%
%\begin{thebibliography}{}
%\softraggedright
%
%\bibitem[Smith et~al.(2009)Smith, Jones]{smith02}
%P. Q. Smith, and X. Y. Jones. ...reference text...
%
%\end{thebibliography}

\end{document}
