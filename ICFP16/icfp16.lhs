\documentclass[numbers]{sigplanconf}

\newif\ifanonymous

%\anonymoustrue
\anonymousfalse

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
%\subtitle{Functional Pearl}

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
There are two approaches to bidirectional programming.
One is the get-based method where one writes |get| and
|put| is automatically derived, and the other is
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
bidirectional language.
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
\end{code}
\end{comment}

\section{Introduction}

Bidirectional transformations are hot! They
originated from the {\em view updating\/} mechanism in the
database community~\cite{Bancilhon:81,Dayal:82,GoPZ88},
and have been recently attracting a lot of attention
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
\item {\em Get-based Method}: allowing users to write |get|
and derive a suitable |put| \cite{Foster2007,MHNHT07,Bohannon:08,Barbosa2010,Hidaka:10,Hofmann2012,Pacheco2012};
\item {\em Put-based Method}: allowing users to write |put|
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
derive intentional update policies of |put|,
in order to deal with various update policies of |put| in
different contexts, significant extensions
to the language for writing |get| are necessary.
As a matter of fact, from the original get-based bidirectional
language \emph{lenses} \cite{Foster2007}, we have seen
many such extensions, e.g., the \emph{matching lenses}
to deal with alignment policies \cite{Barbosa2010},
the \emph{delta lenses} to deal with modification-sensitive update policies
\cite{Diskin:2011,Hofmann2012}, and the \emph{generic lenses} to deal with
any updates on inductive data structures \cite{Pacheco2012}.
All these extensions, as seen in the related papers,
are nontrivial, where one has to
rework all the original lens framework by adding new information
to |get| to indirectly control of the behavior of |put|, and to prove
that the extension is sound in the sense that the new |get| and |put|
are well-behaved.

In this paper, we put up
the slogan ``One |put| for All'', in the sense that
a good language for programming |put| can not only
give full control over the behavior of bidirectional transformations,
but also enable us to systematically
develop various domain-specific bidirectional languages and use
them seamlessly in one framework, which
would be nontrivial with the get-based method as seen above.
After a brief review of BiGUL~\cite{Ko2016}, a putback-based
bidirectional language, we demonstrate how it can be used to
concisely implement the matching/delta/generic lenses that
are guaranteed to be well-behaved.

%%%
%%% Putback-Based Bidirectional Transformations
%%%
\section{Preparation: Putback-Based BX}

%\TODO{Will revise this part later}

%An under-appreciated fact about well-behaved lenses is that \emph{put} completely determines the behavior of the corresponding \emph{get} --- that is, given a \emph{put} function and two \emph{get} functions each of which forms a well-behaved lens when paired with the \emph{put} function, it must be the case that the two \emph{get} functions are pointwise equal. This fact was already noted by Foster in his PhD thesis~\cite{Foster2009} but had remained neglected until people dug up this idea and started exploring the possibility of specifying BXs in terms of \emph{put} \TODO{citations}.

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
The semantics of |Case| is largely as people would expect: executing the first branch whose associated predicate evaluates to true on the current state, and performing further updates when this branch is normal.
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

The simplest alignment strategy is the positional one. The following types for
source (|Source|) and view (|View|) are used for the running example.
%
\begin{code}
type Source  = (Int, (Char, Int))
type View    = (Int, Char)
\end{code}
%
The first |Int| component of the pair should match the first |Int| component of the view,
and the |Char| component of the source should match the |Char|
component of the view. This relation between source and view can be expressed
with the following BiGUL program:
%
\begin{code}
myBX :: BiGUL Source View
myBX = Replace `Prod` $(rearrV   [| \ c -> (c, ()) |])
                                 (Replace `Prod` Skip)
\end{code}

Positional alignment for lists with elements of the above source and view types
is pretty straightforward. No moves are taken into
account, and elements are added or deleted at the end of the source. Just as
with any other programming practice, the BiGUL program must take into account
the several possibilities of source and view values in the update process:
%
\begin{itemize}
  \item both source and view are empty, and we just
    |Skip|;
  \item all elements of the view were processed, so we adapt the source by removing
    the extra elements
    |\ _ _ -> []|;
    \item both source and view have elements, then we update with the head of both
    source and view, and then recurse
    |u `Prod` myMapL c u|;
  \item the source does not have enough elements and create new ones
    |\ _ ((k,v1) : _) -> [(k,(v1,0))]|.
\end{itemize}
%
These actions are packed into a |Case| statement which selects the correct
action for each situation:
%
\begin{code}
myMapL :: BiGUL [Source] [View]
myMapL = Case
  [ $(normalSV [p| [] |] [p| [] |])
      ==> $(rearrV [| \ [] -> () |]) Skip
  , $(adaptiveV [p| [] |])
      ==> \ _ _ -> []
  , $(normalSV [p| (_ : _) |] [p| (_ : _) |])
      ==> $(rearrV [| \ (v:vs) -> (v, vs) |])$
        $(rearrS [| \ (s:ss) -> (s, ss) |])$
          myBX `Prod` myMapL
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

Running the |get| function with this BiGUL program, we obtain the following
result:
%
\begin{lstlisting}
@@>@@ get myMapL [(0,('a',0)),(1,('b',1)),(2,('c',2))]
[(0,'a'),(1,'b'),(2,'c')]
\end{lstlisting}
%
We can perform the changes that we want to this view, e.g., modify the characters
to upper case, and put that view back into the original source\footnote{The
symbol \lstcontinueline{} denotes line continuation.}:
%
\begin{lstlisting}
@@>@@ put myMapL [(0,('a',0)),(1,('b',1)),(2,('c',2))] [(0,'A'),(1,'B'),(2,'C')]
[(0,('A',0)),(1,('B',1)),(2,('C',2))]
\end{lstlisting}
%
Moreover, we can see the limitations of positional update when removing an
element \lstinline!(1,'b')!:
%
\begin{lstlisting}
@@>@@ put myMapL [(0,('a',0)),(1,('b',1)),(2,('c',2))] [(0,'a'),(2,'c')]
[(0,('a',0)),(2,('c',1))]
\end{lstlisting}
%
or adding a new one \lstinline!(3,'d')! before the end:
%
\begin{lstlisting}
@@>@@ put myMapL [(0,('a',0)),(1,('b',1)),(2,('c',2))] [(0,'a'),(1,'b'),(3,'d'),(2,'c')]
[(0,('a',0)),(1,('b',1)),(3,('d',2)),(2,('c',0))]
\end{lstlisting}

The |myMapL| program can be generalized to work on lists with arbitrary values.
For that, it must be parametrized with a \emph{create} function, to produce a
source element from a view one, and with a BiGUL program to be run on the
elements:
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

More complex alignment strategies can be implemented using BiGUL. One example is
a key-based one, where elements of the source and the view are paired based on a
key component from each of the elements.

The idea to implement this strategy is to separate the program in two parts:
%
\begin{itemize}
  \item alignment of the elements;
  \item the actual update.
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
source such that then they are aligned. This is performed by traversing the
view and fetching the first corresponding element in the original source. If
such element is not present, we create it. At the end, source elements not
present in view are discarded. The adaptation of the source can be implemented
as:
%
\begin{code}
keyMatchAdapt s v = Prelude.map getSourceElement v
  where  getSourceElement ve =
           case Prelude.filter ((== fst ve) . fst) s of
             []        -> create ve
             (se : _ ) -> se
         create (k, v1) = (k, (v1, 0))
\end{code}

When the source and the view are aligned, a simple positional update, as defined
in the previous section, can be used. Thus, putting it all together, we obtain a
the following BiGUL program:
%
\begin{code}
myKeyMatch ::  BiGUL [Source] [View]
myKeyMatch = Case
  [ $(normal [| isAligned |]) ==> myMapL
  , $(adaptive [| \ _ _ -> True |]) ==> keyMatchAdapt ]
\end{code}

The result of running the |get| function with |myKeyMatch| is the same as with
|myMapL| since they only differ in the alignment strategy:
%
\begin{lstlisting}
@@>@@ get myKeyMatch @@\lstcontinueline@@
    [(0,('a',0)),(1,('b',1)),(2,('c',2))]
[(0,'a'),(1,'b'),(2,'c')]
\end{lstlisting}
%
Running the |put| function also has the same result when the elements are the
same and the order did not change:
%
\begin{lstlisting}
@@>@@ put myKeyMatch @@\lstcontinueline@@
    [(0,('a',0)),(1,('b',1)), (2,('c',2))] @@\lstcontinueline@@
    [(0,'A'),(1,'B'),(2,'C')]
[(0,('A',0)),(1,('B',1)),(2,('C',2))]
\end{lstlisting}
%
However, when removing elements \lstinline!(1,'b')! or adding new ones
\lstinline!(3,'d')!, key-based alignment is more precise than positional:
%
\begin{lstlisting}
@@>@@ put myKeyMatch @@\lstcontinueline@@
    [(0,('a',0)),(1,('b',1)),(2,('c',2))] @@\lstcontinueline@@
    [(0,'a'),(2,'c'),(3,'d')]
[(0,('a',0)),(2,('c',2)),(3,('d',0))]
\end{lstlisting}
%
Nonetheless, key-based alignment also has its limitations, e.g., when modifying
the key of an element (\lstinline!(1,'b')! to \lstinline!(3,'b')!):
%
\begin{lstlisting}
@@>@@ put myKeyMatch @@\lstcontinueline@@
    [(0,('a',0)),(1,('b',1)),(2,('c',2))] @@\lstcontinueline@@
    [(0,'a'),(3,'b'),(2,'c')]
[(0,('a',0)),(3,('b',0)),(2,('c',2))]
\end{lstlisting}

As with the positional update, this program can be generalized for key-based
alignment on lists with arbitrary contents. For that, the |keyMatch| function
must be parametrized with a function to get a key component from the source, another
function to get the key component from the view, and the create and BiGUL update
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

Alignment can be made more precise using information about how the view is modified.
If we extract the relation of elements in the original
view to the elements in the modified view, then the alignment performed when
updating the source can be completely correct.

The relation of elements in the original view with the ones in the modified view
can be defined by a mapping from the location of the element in the original
artifact to the location of the element in the modified artifact. The location
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
additional information. Implementing this in the running example:
%
\begin{code}
myAlignL'  ::  BiGUL ([Source], Delta) [View]
myAlignL' = Case
  [ $(normal [| \(s, d) v   ->  d == getIdL v
                            &&  d == getIdL s |])
      ==> $(rearrS [| \(s, _) -> s |]) myMapL
  , $(adaptiveS [| const True |])
      ==> \(s,d) v ->  let s' = myAdaptDeltaL s v d
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
myAdaptDeltaL  :: [Source] -> [View] -> Delta
               -> [Source]
myAdaptDeltaL s v d =
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
myAlignL :: Delta -> BiGUL [Source] [View]
myAlignL d = emb g p
  where  g s    = get myAlignL' (s, getIdL s)
         p s v  = fst $ put myAlignL' (s, d) v
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
put myAlignL' (s, getIdL v) (get myAlignL' (s, getIdL s))
== { getIdL v == getIdL s }
put myAlignL' (s, getIdL s) (get myAlignL' (s, getIdL s))
== { GetPut for myAlignL' }
(s, getIdL s)
\end{spec}
%
\textsc{PutGet} -- this law states that the view after updating a source is the
same as the one used for the update. As the result of the |put| function, let
|(s', delta1) = put myAlignL' (s, delta) v|, thus |(s', delta1)| is consistent
with |v| and |delta1 == getIdL s'|. Applying the |get| function~|g|:
%
\begin{spec}
get myAlignL' (s', getIdl s')
== { delta1 = getIdL s' }
get myAlignL' (s', delta1)
== { let binding }
get myAlignL' (put myAlignL' (s, delta))
== { PutGet for myAlignL' }
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
@@>@@ get (myAlignL @@|d1|@@) @@\lstcontinueline@@
    [(0,('a',0)),(1,('b',1)),(2,('c',2))]
[(0,'a'),(1,'b'),(2,'c')]
\end{lstlisting}
%
However, in the put direction, results may vary depending on the given delta,
e.g., no changes are performed (using |d1|):
%
\begin{lstlisting}
@@>@@ put (myAlignL @@|d1|@@) @@\lstcontinueline@@
  [(0,('a',0)),(1,('b',1)),(2,('c',2))] @@\lstcontinueline@@
  [(0,'A'),(1,'B'),(2,'C')]
[(0,('A',0)),(1,('B',1)),(2,('C',2))]
\end{lstlisting}
%
versus a swap between the last two elements (using |d2|):
%
\begin{lstlisting}
@@>@@ put (myAlignL @@|d2|@@) @@\lstcontinueline@@
    [(0,('a',0)),(1,('b',1)),(2,('c',2))] @@\lstcontinueline@@
    [(0,'A'),(1,'B'),(2,'C')]
[(0,('A',0)),(1,('B',2)),(2,('C',1))]
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
@@>@@ put (myAlignL @@|d3|@@) @@\lstcontinueline@@
    [(0,('a',0)),(1,('b',1)),(2,('c',2))] @@\lstcontinueline@@
    [(0,'A'),(1,'B'),(2,'C')]
[(0,('A',0)),(1,('B',1)),(2,('C',0))]
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

Another container where delta alignment can be implemented is a tree. Many kinds
of trees exist, but we use binary tree with labels in the nodes:
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
myAdaptDeltaT  :: Tree Source -> Tree View -> Delta
               -> Tree Source
myAdaptDeltaT s v d = Prelude.fmap idOrCreate (locsT v)
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

The implementation of the positional tree update is similar to the one for
lists, since both have only two data constructors. However, trees have double
recursion which must be taken into account.
%
\begin{code}
myMapT :: BiGUL (Tree Source) (Tree View)
myMapT = Case
  [ $(normalSV [p| Nil |] [p| Nil |])
      ==> $(rearrV [| \ Nil -> () |]) Skip
  , $(adaptiveV [p| Nil |])
      ==> \ _ _ -> Nil
  , $(normalSV [p| Node _ _ _ |] [p| Node _ _ _ |])
      ==>  $(rearrV  [| \ (Node v vl vr)
                       -> (v, (vl, vr)) |]) $
             $(rearrS  [| \ (Node s sl sr)
                         -> (s, (sl, sr)) |])$
                  myBX `Prod` (myMapT `Prod` myMapT)
  , $(adaptiveV [p| (Node _ _ _) |])
      ==> \ _ (Node (k, v1) _ _) -> Node  (k, (v1, 0))
                                          Nil    Nil
  ]
\end{code}

Having the adaptation and the positional update, we can now define a delta-based
alignment for trees in a similar way as with lists:
%
\begin{code}
myAlignT' :: BiGUL (Tree Source, Delta) (Tree View)
myAlignT' = Case
  [ $(normal [| \(s, d) v  ->  d == getIdT v
                           &&  d == getIdT s |])
      ==> $(rearrS [| \(s, _) -> s |]) myMapT
  , $(adaptiveS [| const True |])
      ==> \(s,d) v ->  let s' = myAdaptDeltaT s v d
                       in (s', getIdT v) ]
\end{code}
%
and corresponding wrapper:
%
\begin{code}
myAlignT :: Delta -> BiGUL (Tree Source) (Tree View)
myAlignT d = emb g p
  where  g s    = get myAlignT' (s, getIdT s)
         p s v  = fst $ put myAlignT' (s, d) v
\end{code}

The application of |get| and |put| to trees is similar to the application of
them to lists. The |get| functions takes the source tree and produces a view
tree where its elements are the view of their correspondence in the source:
%
\begin{lstlisting}
@@>@@ get (myAlignT @@|d1|@@) (Node (1,('b',1)) @@\lstcontinueline@@
      (Node (0,('a',0)) Nil Nil) @@\lstcontinueline@@
      (Node (2,('c',2)) Nil Nil))
Node (1,'b')  (Node (0,'a') Nil Nil) @@\lstcontinueline@@
              (Node (2,'c') Nil Nil)
\end{lstlisting}
%
The delta specification in the |put| transformation is the same as with lists:
%
\begin{lstlisting}
@@>@@ put (myAlignT @@|d1|@@) @@\lstcontinueline@@
    (Node (1,('b',1)) @@\lstcontinueline@@
      (Node (0,('a',0)) Nil Nil) @@\lstcontinueline@@
      (Node (2,('c',2)) Nil Nil)) @@\lstcontinueline@@
    (Node (1,'B') @@\lstcontinueline@@
      (Node (0,'A') Nil Nil) @@\lstcontinueline@@
      (Node (2,'C') Nil Nil))
Node (1,('B',1))  (Node (0,('A',0)) Nil Nil) @@\lstcontinueline@@
                  (Node (2,('C',2)) Nil Nil)
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

Delta-based alignment can also be implemented for other containers. The
implementations for the list and tree cases are generalizable to other
containers.

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
For flexibility, these functions are defined in a type class
%
\begin{spec}
class Shapely (t :: * -> *) where
  shape :: t a -> t ()
  data_ :: t a -> [a]
  recover :: (t (), [a]) -> t a
\end{spec}

On top of these functions, it is possible to define new ones, e.g., |locs ::
T a -> Set Loc| to get a all the locations of the data elements within the
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

Starting with the adaptation, we can make use of the functions resulting from
the fact that we can see a container as a shape and data. Therefore, we recover
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

\begin{code}
align'  ::  (Shapely t, Positional t)
        =>  BiGUL s v -> (v -> s)
        ->  BiGUL (t s, Delta) (t v)
align' b c = Case
  [ $(normal [| \(s, d) v  ->  d == getId v
                           &&  d == getId s |])
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
@@>@@ put (keyAlign myBX myCreate fst fst) @@\lstcontinueline@@
    [(0,('a',0)),(1,('b',1)),(2,('c',2))] @@\lstcontinueline@@
    [(0,'A'),(1,'B'),(2,'C')]
[(0,('A',0)),(1,('B',1)),(2,('C',2))]
\end{lstlisting}
%
and for trees:
%
\begin{lstlisting}
@@>@@ put (keyAlign myBX myCreate fst fst) @@\lstcontinueline@@
    (Node (1,('b',1)) @@\lstcontinueline@@
      (Node (0,('a',0)) Nil Nil) @@\lstcontinueline@@
      (Node (2,('c',2)) Nil Nil)) @@\lstcontinueline@@
    (Node (1,'B') @@\lstcontinueline@@
      (Node (0,'A') Nil Nil) @@\lstcontinueline@@
      (Node (2,'C') Nil Nil))
Node (1,('B',1))  (Node (0,('A',0)) Nil Nil) @@\lstcontinueline@@
                  (Node (2,('C',2)) Nil Nil)
\end{lstlisting}
%
where |myCreate (k, v1) = (k, (v1, 0))|.
%
\begin{comment}
\begin{code}
myCreate :: View -> Source
myCreate (k, v1) = (k, (v1, 0))
\end{code}
\end{comment}


%%%
%%% Conclusion
%%%
\section{Conclusion}

We hope to send the following two messages through this %pearl
paper. One is that putback-based programming is not that 
difficult in BiGUL, a simple but powerful put-based bidirectional
language. The other is that a \emph{single} well-designed putback-based
bidirectional programming language can serve as basis for developing
many useful domain-specific bidirectional languages/libraries.
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
