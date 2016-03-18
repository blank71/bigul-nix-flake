\documentclass[preprint,numbers]{sigplanconf}

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
%format Prelude.map=map
%format Prelude.filter=filter
%format Set.map=map
%format Set.findMin=findMin
%format Set.fromList=
%format Set.elems=elems
%format Set.empty=" \emptyset "

\usepackage{amsmath,amssymb,amsfonts}
\usepackage{graphicx}
\usepackage{xcolor}
\usepackage{xspace}
\usepackage{verbatim}
\usepackage{listings}
\lstset{%
	basicstyle=\scriptsize\ttfamily,
	language={Haskell},
	inputencoding=utf8,
	breaklines=true,
	prebreak = \raisebox{0ex}[0ex][0ex]{\ensuremath{\hookleftarrow}},
	morekeywords={},
	deletekeywords={Num},
	keywordstyle=\color[rgb]{0,0,1},             % keywords
	commentstyle=\color[rgb]{0.133,0.545,0.133}, % comments
	stringstyle=\color[rgb]{0.627,0.126,0.941},  % strings
	% escapechar=@,
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

\conferenceinfo{CONF 'yy}{Month d--d, 20yy, City, ST, Country}
\copyrightyear{20yy}
\copyrightdata{978-1-nnnn-nnnn-n/yy/mm}
\copyrightdoi{nnnnnnn.nnnnnnn}

% Uncomment the publication rights you want to use.
%\publicationrights{transferred}
%\publicationrights{licensed}     % this is the default
%\publicationrights{author-pays}

%\titlebanner{banner above paper title}        % These are ignored unless
%\preprintfooter{short description of paper}   % 'preprint' option specified.

\title{The Under-Appreciated Put: Implementing Delta-Alignment in BiGUL}
\subtitle{Functional Pearl}

\ifanonymous
\authorinfo{}{}{}
\else
\authorinfo{Jorge Mendes}
           {HASLab, INESC TEC \& Universidade do Minho, Portugal}
           {jorgemendes@@di.uminho.pt}
%\authorinfo{Name2\and Name3}
%           {Affiliation2/3}
%           {Email2/3}
\fi

\maketitle

\begin{abstract}
  \TODO{Ideas to express: BX in the put direction is precise; more concepts can
  be described. An example of such concept is alignment.}
\end{abstract}

\category{CR-number}{subcategory}{third-level}

% general terms are not compulsory anymore,
% you may leave them out
\terms
term1, term2

\keywords
keyword1, keyword2

%%%
%%% Haskell Preamble
%%%
\begin{comment}
\begin{code}
{-# LANGUAGE TemplateHaskell #-}
module ICFP16 where

import Data.Relation (rngOf)
import Data.Set as Set
import Data.Shape
import Generics.BiGUL.AST
import Generics.BiGUL.Interpreter.Unsafe (get, put)
import Generics.BiGUL.TH
import GHC.Generics
import Prelude hiding (traverse)
\end{code}
\end{comment}

\section{Introduction}

Bidirectional transformations are hot! They are 
originated from the {\em view updating\/} mechanism in the
database community~\cite{Bancilhon:81,Dayal:82,GoPZ88},
have been recently attracting a lot of attention
from researchers in the communities of programming languages and 
software engineering \cite{GRACE:09,HSST11},
since the pioneering work of Foster et al. on 
a combinatorial language for bidirectional tree transformations \cite{Foster2007}.

A bidirectional transformation (BX for short) is simply
a pair of functions
< get :: Source -> View
< put :: Source -> View -> View
where 
the \emph{get} function extracts a view from a source and the \emph{put}
function updates the original source with information from the new view.
As a simple example, consider that we wish to synchronize between
rectangles and their heights, we can define
< getHeight (height, width) = height
< putHeight (height, width) height' = (height', width)
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
and derive the unique |get| if there is \cite{PaHF14,PachecoZH14,HuPF14,FischerHP15,Ko2016}.
\end{itemize}

The get-based method has been intensively studied for over ten years
and got much appreciated mainly because |get| is easy to write.
In contrast, the put-based method is new and far from being appreciated,
and the main critism is two fold. First, that |put| is difficult to write


The big advantage of the get-based method is that
it is user-friendly; |get| is much easier to write than |put|.

attractive, not only because it
stems from the traditional view updating problem (in the database community)
where |get| is given as a query beforehand, but also because
|get| is easy to write.
However, the get-based method cannot describe in general full behavior
of bidirectional transformation, so automatically
derived |put| limitation may not match the prgorammers' intension
but the progammers have no ways to express their intension unless
the |get| language 

prevent from it from being used in practice.
First, for an non-injective |get|
there usually exist many possible |put| functions that can be
combined with it to form a valid BX. For instance, for the same |getHeight|,
the following is a valid |put| too:
< putHeight1 (height, weight) height'
<      = (height', weight x (height' / height))
%< putHeight2 (height, weight) height'
%<      | height==height'  = (height, width)
%<      | otherwise        = (height', 1)
In fact, it is impossible to automatically derive
the most suitable valid |put| 
that can be paired with the |get| to form a bidirectional
transformation \cite{Jeremy-bx05}.
This means that theoretically |get| does not contain
sufficient information for a system to automatically
derive intentional update policies of |put|,
so in order to deal with various update policies of |put| in 
different contexts, nontrivial extensions
are necessary to make on the language for writing |get|.
For instance, the original get-based bidirectional
language |lenses| in \cite{Foster2007} is extended to the |matching lenses|
to deal with alignment policies \cite{Barbosa2010},
to the |delta lenses| to deal with operation-based update policies
\cite{Diskin:2011,Hofmann2012}, and to the |generic lenses| to deal with
any updates on inductive data structures \cite{Pacheco2012}.

The put-based method, on the other hand, can solve the above problem,
because for each |put|, if there exists a valid |get| then such |get|
is unique. In other words, |put| can describe all intentions of bidirectional
transformation since |get| is fully determined by |put|.
However, the put-based method is less appreciated.
This is not without reason: as argued in \cite{Foster:09}, 
it is far from being straightforward to
construct a framework that can directly support putback-based
bidirectional programming.

In this pearl paper, we show that the put-based method should deserve
more appreciation.
\TODO{Should continue revision from here}
... the new libraries for
matching lenses, editing/delta lenses,
generic lenses ... become much more easier to constructed
under the put-based framework ... In the get-based approach, we cannot
foresee what additional information should be added to control the put
behavior in the future, so if we want to add new information to control
new put behavior, we will have to reconstruct all the get-library and
prove all again ...


%%%
%%% Putback-Based Bidirectional Transformations
%%%
\section{Preparation: Putback-Based BX}

\TODO{Will revise this part later}

An under-appreciated fact about well-behaved lenses is that \emph{put} completely determines the behavior of the corresponding \emph{get} --- that is, given a \emph{put} function and two \emph{get} functions each of which forms a well-behaved lens when paired with the \emph{put} function, it must be the case that the two \emph{get} functions are pointwise equal. This fact was already noted by Foster in his PhD thesis~\cite{Foster2009} but had remained neglected until people dug up this idea and started exploring the possibility of specifying BXs in terms of \emph{put} \TODO{citations}.

Intuitively, think of a BiGUL program of type \lstinline{BiGUL s v} as describing how to manipulate a state consisting of a source component of type~\lstinline{s} and a view component of type~\lstinline{v}; the goal is to copy all information in the view to proper places in the source.
In the simplest case, the view has type \lstinline{()} and contains no information, and we can use \lstinline{Skip :: BiGUL s ()} to leave the source unchanged;
another simple case is when the view has the same type as the source, and we can use \lstinline{Replace :: BiGUL s s} to replace the entire source with the view.
BiGUL programs compose --- for example, when both the source and the view are pairs, we can use
\begin{lstlisting}
Prod :: BiGUL s v -> BiGUL s' v' ->
        BiGUL (s, s') (v, v')
\end{lstlisting}
to compose two BiGUL programs on the left and right components respectively.
Of course, in most cases the source and view are in more complex forms, and we should somehow transform and decompose them into simpler forms before we can use \lstinline{Skip}, \lstinline{Replace}, or \lstinline{Prod}; this is usually done using two ``rearrangement'' operations on the source and view respectively:
We can use the source rearranging operation
\begin{lstlisting}
$(rearrS [| f |]) :: BiGUL s' v -> BiGUL s v
\end{lstlisting}
where \lstinline{f}~is a ``simple'' $\lambda$-expression of type \lstinline{s -> s'} for extracting from the source of type~\lstinline{s} a (usually smaller) source of type~\lstinline{s'} before performing further updates on the extracted source, or dually the view rearranging operation
\begin{lstlisting}
$(rearrV [| g |]) :: BiGUL s v' -> BiGUL s v
\end{lstlisting}
where the ``simple'' $\lambda$-expression \lstinline{g} should have type \lstinline{v -> v'}, and is used to transform the view from type~\lstinline{v} to type~\lstinline{v'} before performing further updates.

Most expressiveness of BiGUL comes from its \lstinline{Case} operation for performing case analysis:
\begin{lstlisting}
Case :: [(s -> b -> Bool, Branch s v)] -> BiGUL s v
\end{lstlisting}
\lstinline{Case} takes a list of pairs whose first component is a boolean predicate on both the source and the view, and whose second component is a ``branch''.
A branch can be a ``normal'' branch, in which case it is a BiGUL program of type \lstinline{BiGUL s v}, or an ``adaptive'' branch, in which case it is a Haskell function of type \lstinline{s -> v -> s}.
The semantics of \lstinline{Case} is largely as people would expect: executing the first branch whose associated predicate evaluates to true on the current state, and performing further updates when this branch is normal.
More interestingly, when the chosen branch is adaptive, the source will be replaced by the result of evaluating the associated function on the current state and the whole \lstinline{Case} will be executed again.

%%%
%%% Positional Alignment
%%%
\section{Positional Alignment}

\begin{code}
type Source = (Int, (Char, Int))
type View = (Int, Char)
\end{code}

\begin{code}
myBX :: BiGUL Source View
myBX = Replace `Prod` $(rearrV   [| \ c -> (c, ()) |])
                                 (Replace `Prod` Skip)
\end{code}

The simplest alignment strategy is the positional one. No moves are taken into
account, and elements are added or deleted at the end of the source. Just as
with any other programming practice, the BiGUL program must take into account
the several possibilities of source and view values in the update process:
%
\begin{itemize}
  \item both source and view are empty, and we just
    |Skip|;
  \item all elements of the view were processed, so we adapt the source removing
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

When both source and view are empty, or both have elements, a BiGUL program can
be applied. When both are empty is the terminal case, yielding the empty list.
When both have values, the head of the source is updated with the head of the
view, and then recursion is performed.

In the other two cases, adaptation of the source is required. The first one is
when the view is empty, and the source is modified to be the empty list. After
this adaption, the |Case| statement looks for a normal branch to apply, entering
in the one where both source and view are empty. The second case is when the
view still has elements, but the source is empty. In this case, a new source
element is created from the source element at the head of the list. Then, the
|Case| statement looks for a normal branch, entering in the one where both
source and view have elements, updating the heads and recursing.

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
  \item aligment of the elements;
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
elements, and that the keys match element wise.

In the case that both lists are not aligned, we define a function that adapts a
source such that then they are both aligned. This is performed by traversing the
view and fecthing the first corresponding element in the original source. If
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

As with the positional update, this program can be generalized for key-based
alignment on lists with arbitrary contents. For that, the |keyMatch| function
must be parametrized with function to get a key component from the source, another
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

Alignment can be made more precise using information about the operations
applied to the view. If we extract the relation of elements in the original
view to the elements in the modified view, then the alignment performed when
updating the source can be completely correct.

%%% Containers as Shape and Data
\subsection{Containers as Shape and Data}

\citet{Pacheco2012} rely on types with explicit notion of shape and data in
their delta-alignment over inductive types, a
property provided by polymorphic data types in functional programming.
Moreover, they applied a notation from \emph{shapely types}~\cite{jay1995} in
order to have tools to work with these data types.
Employing these concepts, one can abstract from the shapes of both source and
view, and just take the data into account for the alignment process.

Thus, a polymorphic type \(T~a\) can be characterized by three functions:
|shape :: T a -> T ()| to extract the shape;
|data_ :: T a -> [a]| to extract the data;
and, |recover :: (T (), [a]) -> T a| to rebuild the type value
from its shape and data.

\begin{comment}
\begin{code}
type Loc = Int
\end{code}
\end{comment}
%
On top of these functions, it is possible to define new ones, e.g., |locs ::
T a -> Set Loc| to get a all the locations of the data elements within the
container.

%%% Delta Alignment
\subsection{Delta Alignment}

Before implemeting delta-based alignment, let us define what a delta is. Using
the containers as specified in the previous section, each element is indexed by
a location in the container. Moreover, it is easier to define a relation from
elements in an artifact to an element in another element than describing which
elements were added and which ones were deleted. Thus, we define a delta a set
of pair of locations between two artifacts:
%
\begin{code}
type Delta = Set (Loc, Loc)
\end{code}

Furthermore, we need a method to determine from a delta if some artifact has
suffered any positional change (movement within the container, addition, or
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
getId :: [a] -> Delta
getId = Set.map (\ l -> (l, l)) . locs
\end{code}

%%% Delta Alignment for Lists
\subsection{Delta Alignment for Lists}

In order to implement such kind of alignment in BiGUL, the delta can be inserted
into the source, since we are able to manipulate it using adaptation in
|Case| branches.

The implementation of delta-based alignment is similar to the key-based one:
%
\begin{enumerate}
  \item modification of the source aligning to the view using a delta;
  \item a positional update.
\end{enumerate}
%
However, the delta in the source introduces a bit more complexity to deal the
additional information:
%
\begin{code}
align'  ::  BiGUL s v -> (v -> s)
        ->  BiGUL ([s], Delta) [v]
align' b c = Case
  [ $(normal [| \(_, d) v -> d == getId v |])
      ==> $(rearrS [| \(s, _) -> s |]) (mapL c b)
  , $(adaptiveS [| const True |])
      ==> \(s,d) v ->  let s' = adaptDeltaL c s v d
                       in (s', getId v) ]
\end{code}
%
An alternative |Case| statement is used to check which of these two steps are to
be performed. This is done based on the changes performed on the view: if no
changes were performed, the delta maps each element's position to the same
position, i.e., the identity delta.
Otherwise, a
transformation is performed on the source to rearrange the elements based on the
delta, create missing view elements, and
delete no longer existent view elements:
%
\begin{code}
adaptDeltaL :: (v -> s) -> [s] -> [v] -> Delta -> [s]
adaptDeltaL c s v d = Prelude.map idOrCreate (Set.elems $ locs v)
  where  idOrCreate i =  let js = rngOf i d
                         in  if js /= Set.empty
                             then data_ s !! Set.findMin js
                             else c (data_ v !! i)
\end{code}
%
Note that in |align'| the create function |c| given to |mapL| is not required since
|adaptDeltaL| creates the missing elements.

However, having the delta paired with the source might be inconvenient. To solve
such situation, a wrapper is made that takes care of dealing with the delta:
%
\begin{code}
align  :: Eq v
       => BiGUL s v -> (s -> v) -> Delta
       -> BiGUL [s] [v]
align b c d = emb g p
  where  g s    = get (align' b c) (s, getId s)
         p s v  = fst $ put (align' b c) (s, d) v
\end{code}
%
This wrapper implements directly the |get| and |put| functions, and
embeds them into a BiGUL program.

The embedding of |get| and |put| functions can be defined as a BiGUL program:
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
In order for an embedding to be well-behaved, running the |put| function should
produce a source that when running |get| should return the view given to the
former, as stated by the \textsc{GetPut} law and enforced by the case structure.
Furthermore, the view should be completely defined by the source.


%%%
%%% Delta-Based Tree Alignment
%%%
\section{Delta-Based Tree Alignment}

Delta-based alignment can also be implemented for other containers. The
implementation for the list case is easily generalizable in some parts, and the
structure of the |align'| can also be kept. Thus, two parts must be modified:
the adaptation, and the positional update.

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

The other part is the positional update. Before implementing it, let us define
a tree data structure:
%
\begin{code}
data Tree a = Nil | Node a (Tree a) (Tree a)
\end{code}
\begin{comment}
\begin{code}
instance Generic (Tree a) where
      type Rep (Tree a) = (:+:) U1 ((:*:) (K1 R a) ((:*:) (K1 R (Tree a)) (K1 R (Tree a))))
      from Nil = L1 U1
      from (Node var_arJr var_arJs var_arJt)
        = R1 ((:*:) (K1 var_arJr) ((:*:) (K1 var_arJs) (K1 var_arJt)))
      to (L1 U1) = Nil
      to (R1 ((:*:) (K1 var_arJr) ((:*:) (K1 var_arJs) (K1 var_arJt))))
        = Node var_arJr var_arJs var_arJt
$(return [])
\end{code}
\end{comment}
%
This data structure presents similarities with lists, were both have only two
constructors. However, trees have double recursion. Taking the positional
mapping implemented for lists, a generic one for this tree data structure can be
defined as:
%
\begin{code}
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
\end{code}

Having the adaptation and the positional update, we can now define a delta-based
alignment for trees in a similar way as with lists:
%
\begin{code}
alignT'  ::  BiGUL a b -> (b -> a)
         ->  BiGUL (Tree a, Delta) (Tree b)
alignT' b c = Case
  [ $(normal [| \(_, d) v -> d == getId v |])
      ==> $(rearrS [| \(s, _) -> s |]) (mapT c b)
  , $(adaptiveS [| const True |])
      ==> \(s,d) v ->  let s' = adaptDelta c s v d
                       in (s', getId v) ]
\end{code}
%
and corresponding wrapper:
%
\begin{code}
alignT  :: Eq v
        => BiGUL s v -> (s -> v) -> Delta
        -> BiGUL (Tree s) (Tree v)
alignT b c d = emb g p
  where  g s    = get (alignT' b c) (s, getId s)
         p s v  = fst $ put (alignT' b c) (s, d) v
\end{code}

%%%
%%% Other Matching Algorithms Built Upon Deltas
%%%
\section{Other Matching Algorithms Built Upon Deltas}

With the implementation of delta-based alignment, we can implement other
alignment strategies upon the deltas without much work.
It is possible to make minor changes to the |align| function to
implement other kinds of alignments, e.g., key-based (for the special case of
lists):
%
\begin{code}
keyAlign :: (Shapely s, s ~ [], Eq b, Eq k)
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


%%%
%%% Conclusion
%%%
\section{Conclusion}

\clearpage

%%%
%%% Introduction
%%%
\section{Introduction}

Several approaches exist to help dealing with specific situations when
developing software. One such approach consists in the use of bidirectional
transformation (BX) mechanisms to maintain consistency between two pieces of
related information.

Some work on BXs emerges from the view-update problem, where a view is generated
from a source database and consistency must be kept between these two artefacts.
If the view suffers changes, these should be reflected in the source database.

The \emph{lens} framework~\cite{Greenwald2003} emerged to solve similar
problems, where a \emph{get} function creates a abstract view from a concrete
source, and a \emph{put} function provides an updated source using the original
source and the modified view.

To define a BX system, one has to provide a \emph{get} and a \emph{put}
functions, ensuring that some properties are statisfied by this pair of
functions. These properties ensure the \emph{well-behavedness} of the BX system.

Research was done in order to derive a suitable \emph{put} for a given
\emph{get} in order to help the development of BXs. This has some limitations,
since the \emph{put} direction is usually the problematic one.

%
% PUT-BASED BX
%

\TODO{Start introducing BiGUL~\cite{Ko2016} with a very simple BX program.}
%
\begin{code}
type Source = (Int, (Char, Int))
type View = (Int, Char)
\end{code}
\begin{code}
myBX :: BiGUL Source View
myBX = Replace `Prod` $(rearrV   [| \ c -> (c, ()) |])
                                 (Replace `Prod` Skip)
\end{code}

\TODO{Simplify following code, specifying its types. Reuse this program in the
alignment example, thus removing the need for parameters in aligment functions.}

%
% POSITIONAL ALIGNMENT
%

An example of a get program is the projection of a map structure, selecting its
key and part of its value:
%
\[ \mathcal M (K, (V_1, V_2)) \longrightarrow \mathcal M (K, V_1) \]
%
This has several possible \emph{put} functions that would satisfy the
\emph{well-behavedness} properties. This situation can be easily solved by
writing the \emph{put} function and derive the one. Using BiGUL, a language with
such purpose, one can write a simple example that performs the same actions as
the default \emph{put} usually derived from the \emph{get} function, i.e.,
update elements positionally, adding or deleting elements at the end of the
list:
%
\begin{code}
mapLExample  ::  (View -> Source)
             ->  BiGUL Source View
             ->  BiGUL [Source] [View]
mapLExample c u = Case
  [ $(normalSV [p| [] |] [p| [] |])$
      $(rearrV [| \ [] -> () |]) Skip
  , $(adaptiveV [p| [] |])$ \ _ _ -> []
  , $(normalSV [p| (_ : _) |] [p| (_ : _) |])$
      $(rearrV [| \ (v:vs) -> (v, vs) |])$
        $(rearrS [| \(s:ss) -> (s, ss) |])$
          u `Prod` mapLExample c u
  , $(adaptiveV [p| (_ : _) |])$
    \ _ (v : _) -> [c v]
  ]
\end{code}
%
\begin{comment}
\begin{code}
mapL :: (v -> s)
     -> BiGUL s v
     -> BiGUL [s] [v]
mapL c u = Case
  [ $(normalSV [p| [] |] [p| [] |])$ $(rearrV [| \ [] -> () |]) Skip
  , $(adaptiveV [p| [] |])$ \ _ _ -> []
  , $(normalSV [p| (_ : _) |] [p| (_ : _) |])$
      $(rearrV [| \ (v:vs) -> (v, vs) |])$
        $(rearrS [| \(s:ss) -> (s, ss) |])$
          u `Prod` mapL c u
  , $(adaptiveV [p| (_ : _) |])$ \ _ (v : _) -> [c v]
  ]
\end{code}
\end{comment}
%
This program is generic for any source of type \((K, (V_1, V_2))\) and view \(K,
V_1\). Thus it must be parametrized with a create function to create the default
values and a BiGUL udpate program for the elements in the container.

\TODO{Move the ``The Alignment Problem'' section to here in order to introduce
the concept?}

%
% KEY-BASED ALIGNMENT
%

One way to improve a get-based transformation is to annotate it in order
to select a way to perform the \emph{put} operation:
%
\[ \mathcal M (K, (V_1, V_2)) \xrightarrow{\text{\small best match on \(K\)}} \mathcal M (K, V_1) \]
%
This provides information on how to align the elements in the \emph{put}
direction, which is based on a key (\(K\)) in this example. A similar program
can be written in the \emph{put} direction:
%
\begin{code}
keyMatch  ::  BiGUL [Source] [View]
keyMatch  = Case
  [ $(normal [| isAligned |]) (mapL create myBX)
  , $(adaptive [| \ _ _ -> True |]) kalign ]
  where  isAligned s v = length s == length v
           && and (zipWith kmatch s v)
         kmatch se ve = fst se == fst ve
         kalign s v = Prelude.map (getSourceElement s) v
         getSourceElement s ve =
           case Prelude.filter ((== fst ve) . fst) s of
             []        -> create ve
             (se : _ ) -> se
         create (k, v1) = (k, (v1, 0))
\end{code}
%
This \emph{put} program makes use of BiGUL \emph{case} constructor, where an
adaption of the source is made when the source is not aligned with the view.

\TODO{Say that, with BiGUL, the developer implements the alignment strategy
wanted, and does not have to rely on it being implemented in the BX framework.}

\TODO{Maybe move this to a previous point.}
But it is not enough: how to deal with new elements? One can provide
another annotation:
%
\[ \mathcal M (K, (V_1, V_2 = v_2)) \xrightarrow{\text{\small best match on \(K\)}} \mathcal M (K, V_1) \]
%
where \(v_2\) is a default value for type \(V_2\).

%
% PUT-BASED BX
%

Another approach is writing the \emph{put} function. This is more difficult than
writing the \emph{get} function, but it removes the need for extra annotations.
The \emph{put} function has access to both the original source and the modified
view, i.e., all the possible information available to write a program that
provides an updated source. The program, in this example, includes the logic
that leads to the alignment strategy and the default value to use for new
elements. Moreover, an unique \emph{get} function can be derived from this
\emph{put}.
%
\[ \mathcal M (K, (V_1, V_2)) \longleftarrow \mathcal M (K, (V_1, V_2)) \times \mathcal M (K, V_1) \]

%
% DELTA-BASED ALIGNMENT
%

% Motivation for delta-based alignment.
This example continues to have some drawbacks. The key-based alignment might not
reflect the operations performed to the view, resulting in an incorrect
alignment. Having information about the operations performed to the view, it
should be possible to provide a relation of the elements from the original view
that are also present in the modified view. Using this relation, or
\emph{delta}, it is possible to precisely align the elements in the modified
view with the ones in the original source for the \emph{put} operation.
%
\[ \mathcal M (K, (V_1, V_2)) \longleftarrow \mathcal M (K, (V_1, V_2)) \times \mathcal M (K, V_1) \times \Delta \]

\TODO{Goal of the paper. Show that defining the \emph{put} direction has its
benefits and can be more intuitive for certain operations. Moreover, it shows
how to use additional information, namely the delta, that isn't defined in the
put operation, but in is given at runtime instead.}

\begin{comment}
In the next sections, an overview on bidirectional transformations and the
alignment problem is provided. Then, putback-based bidirectional transformation
techniques are presented, followed by an implementation of alignment using such
technique.
\end{comment}


%%%
%%% Bidirectional Transformations
%%%
\section{Bidirectional Transformations}

A successful language to specify BX systems is the \emph{lenses}
language~\cite{Greenwald2003}. A lens \(l : S \leftrightarrow V\), with source
type \(S\) and view type \(V\), is composed by two functions:
%
\begin{align*}
  \bxget &:: S \rightarrow V\\
  \bxput &:: S \rightarrow V \rightarrow S
\end{align*}
%
The \emph{get} function extracts a view from a source and the \emph{put}
function updates the original source with information from the new view.

When developing a BX system, one expects it to be \emph{well-behaved}, i.e.,
that performing certain actions should provide a stable result. One of these
actions is updating a source with an unmodified view of such source, which
should result in the same source. Another action is getting the view after
updating a source, which should result in the same view used for the update.
From these actions and respective results, two laws were defined:
\textsc{PutGet}, for the former action; and, \textsc{GetPut}, for the latter.

For the lenses framework, in order a BX system to be considered
\emph{well-behaved}, the following two laws must be ensured:
%
\begin{align*}
  \bxget \left(\bxput s~v\right) = v
    \tag{\sc GetPut}\label{eq:getput}\\
  \bxput s\,\left(\bxget s\right) = s
    \tag{\sc PutGet}\label{eq:putget}
\end{align*}
%
The \ref{eq:getput} law states that after performing an update to the original
source, the view obtained from this result should be the same as the one used to
perform the update. The \ref{eq:putget} law states that updating the source with an
unchanged view should result in the original source.

\noindent\TODO{
  \begin{itemize}
    \item get is easier to write than put. When writing get, a put can be
      derived, but, since it may be not unique, some assumptions are made, and
      in some cases update policies must be provided.
      Where is this information available?
  \end{itemize}
}

%%
%% TODO (maybe)
%% very well-behaved lenses (it is worth to mention?)
%%  - the create function
%%  - variations from other languages (matching lenses, delta lenses,~\dots)
%%


%%%
%%% The Alignment Problem
%%%
\section{The Alignment Problem}

Alignment consists in matching elements in the source container with elements in
the source container. When modifying a view, the elements in a container might
be modified, e.g., new elements are added, others are deleted, or some are moved
within the container. Many examples of containers exist, with lists and trees
being the more common.

\begin{figure}[ht]
  \centering
  \input{./figures/alignment1}
  \caption{Example of a view, the changes applied to it, and the obtained
  result. Other sets of operations can result in the same view.}
  \label{fig:alignment}
\end{figure}

Unexpected results can be obtained when container elements are not properly
aligned. Most of these issues are consequences of the alignment approach
selected, which include the following ones:
%
% Kinds of alignments
% - [implicitly] positional
% - arbitrary algorithm
% - delta-based
% - operation-based
%
\begin{itemize}
  \item positional update;
  \item use of an arbitrary matching algorithm (e.g., best match);
  \item delta-based alignment; and,
  \item operation-based BX.
\end{itemize}

A positional update of the elements removes elements at the start/end of the source
if it contains more elements than the view, or adds new elements at the
start/end of the source if the view have more elements. Here, start/end is an
arbitrary position within the source. The move of elements is not taken into
account. Using the example in Fig.~\ref{fig:alignment}, a positional update
would be equivalent to a modification of \(v_1\) to \(v_2\), and a change of
\(k_2~v_2\) to \(k_3~v_3\). Thus, the alignment does not reflect the operations
performed to the view.

Using an algorithm to match elements of the original source with elements of the
new view can provide more precision than the positional update. A common
strategy is key-based matching, where a key is used to identify the elements
in the container. With the example in Fig.~\ref{fig:alignment}, one can use the
\(k\) part of the element as a key, resulting in an alignment equivalent to the
modification of \(v_1\) to \(v_2\), the removal of \(k_2~v_2\) and the addition
of \(k_3~v_3\). This alignment also does not reflect the operations performed to
the view, but it is closer than the positional update.

Using information about changes in the view (i.e., \emph{deltas}) is one of the
approaches so that
the elements can be matched accurately between the original source and the
new view. This can be implemented in distinct fashions, one of them identifying
the relation of the elements in the original view with the ones in the modified
view. The elements that are not in this relation were either deleted (if not
present in the modified view) or added (if not present in the original view).

Finally, it is also possible to work with operations, matching operations
performed on the view with operations to be performed on the source.

The first two approaches might not reflect the actual changes performed to the
view, which can introduce some misalignment of the elements of the view with the
source ones. Moreover, these approaches are implicit in some frameworks, or
require additional annotations in the programs. On the other hand, the last two
options use information of the
actual changes or operations performed, resulting in a precise alignment.
However, this information is not always available thus preventing the use of
the last two precise options in some situations. Furthermore, these approaches
differ from the traditional lenses, where more information should be provided
(in the case of the deltas), or the complete system logic is flipped and the BX
system works with operations instead of the usual artefacts.

\mydraft{In the concrete example of matching lenses~\cite{Barbosa2010}, the
original definition of lenses is extended with another function |res :: S -> C|
(``residue''), that maps a source to complement, which consists in information
not present in the view and that is necessary for the update process. Moreover,
this complement is formed by two components: a rigid complement that stores the
chunks; and a resource that maps chunk locations to chunk contents. On top of
this machinery, new laws are added (\textsc{GetChunks}, \textsc{ResChunks},
\textsc{ChunkPut}, etc.).}

\TODO{From State- to Delta-Based Bidirectional Model Transformations}

\TODO{Delta lenses over inductive types.}

\begin{comment}

\noindent\TODO{
\begin{itemize}
  \item Background/related work to understand the work presented in this paper.
  \item From ``Deltas over Polymorphic Inductive Types''
    \begin{itemize}
      \item Functors
      \item Positions
      \item Deltas
    \end{itemize}
  \item Shapely type functions:
    \begin{itemize}
      \item shape
      \item data
      \item recover
    \end{itemize}
\end{itemize}
}

\noindent\TODO{
\begin{itemize}
  \item Description of mapping elements from the view to elements on the source.
  \item In the get direction, position of elements does not change. There is a
    one-to-one mapping.
  \item In the put direction, the source is recovered using its shape and the
    updated data from the original source with the new view using the
    information from the delta.
\end{itemize}
}

\end{comment}

%%%
%%% Alignment as a put Program
%%%
\section{Alignment as a \emph{put} Program}

Alignment is a process performed when the source is updated with the new view.
Thus, it falls naturally in the process of writing a \emph{put} program.

\noindent\TODO{More text motivating writing alignment in a put program.
Introduction for the next subsections.}

\begin{comment}
%%% Positional Update for Lists
\subsection{Positional Update for Lists}

An implementation of positional mapping on lists is presented in
Listing~\ref{lst:posmapl}. This implementation receives a function to create new
source elements when a new view element is added, and a BiGUL program to perform
the element update. It is specified for the several situations that can occur:
\begin{enumerate}
  \item\label{item:posmap1} both view and source are empty;
  \item\label{item:posmap2} view is empty but source has elements;
  \item\label{item:posmap3} both view and source have elements;
  \item\label{item:posmap4} view has elements but source is empty.
\end{enumerate}

The content of both the view and the source are checked with the \emph{case}
construct, where each of the alternatives checks for one of the possible
situations following the given order. In situation~\ref{item:posmap1}, a
\emph{skip} is performed since
there are no elements to update. In situation~\ref{item:posmap2}, the content of
the source is discarded, and a new empty source is used to match the empty view.
This results in the removal of elements that are not present in the view. In
situation~\ref{item:posmap3}, normal element wise update is performed. Finally,
in situation~\ref{item:posmap4}, the empty source is transformed in a new source
with only one element that is not used since it is replace by the value from the
view.

\begin{lstlisting}[caption={Positional mapping of lists.},label={lst:posmapl}]
mapL :: (v -> s)
     -> BiGUL s v
     -> BiGUL [s] [v]
mapL c u = Case
  [ $(normalSV [p| [] |] [p| [] |])$
      $(rearrV [| \ [] -> () |]) Skip
  , $(adaptiveV [p| [] |])$ \ _ _ -> []
  , $(normalSV [p| (_ : _) |] [p| (_ : _) |])$
      $(rearrV [| \ (v:vs) -> (v, vs) |])$
        $(rearrS [| \(s:ss) -> (s, ss) |])$
          u `Prod` mapL c u
  , $(adaptiveV [p| (_ : _) |])$
    \ _ (v : _) -> [c v]
  ]
\end{lstlisting}

Positional mapping does not take into account changes in the model, except for
added or deleted elements that are dealt with at the end of the new source.
However, it is useful to map elements when the source is modified to correspond
to the view in the alignment process.
\end{comment}

%%% Containers as Shape and Data
\subsection{Containers as Shape and Data}

\citet{Pacheco2012} rely on types with explicit notion of shape and data in
their delta-alignment over inductive types, a
property provided by polymorphic data types in functional programming.
Moreover, they applied a notation from \emph{shapely types}~\cite{jay1995} in
order to have tools to work with these data types.
Employing these concepts, one can abstract from the shapes of both source and
view, and just take the data into account for the alignment process.

Thus, a polymorphic type \(T~a\) can be characterized by three functions:
|shape :: T a -> T ()| to extract the shape;
|data_ :: T a -> [a]| to extract the data;
and, |recover :: (T (), [a]) -> T a| to rebuild the type value
from its shape and data.

\begin{comment}
\begin{code}
type Loc = Int
\end{code}
\end{comment}
%
On top of these functions, it is possible to define new ones, e.g., |locs ::
T a -> Set Loc| to get a all the locations of the data elements within the
container.

%%% Delta Alignment
\subsection{Delta Alignment}

Before implemeting delta-based alignment, let us define what a delta is. Using
the containers as specified in the previous section, each element is indexed by
a location in the container. Moreover, it is easier to define a relation from
elements in an artifact to an element in another element than describing which
elements were added and which ones were deleted. Thus, we define a delta a set
of pair of locations between two artifacts:
%
\begin{code}
type Delta = Set (Loc, Loc)
\end{code}

Furthermore, we need a method to determine from a delta if some artifact has
suffered any positional change (movement within the container, addition, or
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
getId :: [a] -> Delta
getId = Set.map (\ l -> (l, l)) . locs
\end{code}

%%% Delta Alignment for Lists
\subsection{Delta Alignment for Lists}

In order to implement such kind of alignment in BiGUL, the delta can be inserted
into the source, since we are able to manipulate it using adaptation in
\emph{case} branches.
%
\begin{code}
align'  ::  BiGUL a b -> (b -> a)
        ->  BiGUL ([a], Delta) [b]
align' b c = Case
  [ $(normal [| \(_, d) v -> d == getId v |])$
      $(rearrS [| \(s, _) -> s |])$ mapL c b
  , $(adaptiveS [| const True |])$
      \(s,d) v ->  let s' = putMapD c s v d
                   in (s', getId v) ]
\end{code}
%
Note that the create function |c| given to |mapL| is not required since
|putMapD| creates the missing elements.

Thus, the delta-based alignment process is done in two steps:
%
\begin{enumerate}
  %\item Creation of new elements and removal of deleted elements.
  \item Modification of the source aligning to the view using a delta.
  \item Positional update.
\end{enumerate}
%
An alternative case statement is used to check which of these two steps are to
be performed. This is done based on the changes performed on the view: if no
changes were performed, the delta maps each element's position to the same
position, i.e., the identity delta.
Otherwise, a
transformation is performed on the source to rearrange the elements based on the
delta, create missing view elements, and
delete no longer existent view elements:
%
\begin{code}
putMapD :: (b -> a) -> [a] -> [b] -> Delta -> [a]
putMapD c s v d = fst (traverse aux (v,0))
  where  aux (vi, i)  | Set.size js > 0 = (si, succ i)
                      | otherwise = (c vi, succ i)
           where  js = rngOf i d
                  si = data_(s) !! (Set.findMin js)
\end{code}

However, having the delta paired with the source might be inconvenient. To solve
such situation, a wrapper is made that takes care of dealing with the delta:
%
\begin{code}
align  :: Eq b
       => BiGUL a b -> (b -> a) -> Delta
       -> BiGUL [a] [b]
align b c d = emb g p
  where  g s    = get (align' b c) (s, getId s)
         p s v  = fst $ put (align' b c) (s, d) v
\end{code}
%
This wrapper implements directly the \emph{get} and \emph{put} functions, and
embeds them into a BiGUL program.

The embedding of |get| and |put| functions can be defined as a BiGUL program:
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
In order for an embedding to be well-behaved, running the |put| function should
produce a source that when running |get| should return the view given to the
former, as stated by the \textsc{GetPut} law and enforced by the case structure.
Furthermore, the view should be completely defined by the source.

\begin{comment}
\TODO{Listing~\ref{lst:putmapd} does the put direction:}

\begin{lstlisting}[caption={Mapping of elements between to containers of the same type using a delta.},label={lst:putmapd}]
putMapD
 :: (b -> a) -- Function to create a missing source
 -> [a]           -- Source
 -> [b]           -- View
 -> Delta [b] [b] -- View delta
 -> [a]
putMapD c s v dV = fst (traverse aux (v,0))
 where aux (vi, i) | Set.size js > 0 = (si, succ i)
                   | otherwise = (c vi, succ i)
         where js = rngOf i d
               si = data_(s) !! (Set.findMin js)
               d = Set.fromList dV
\end{lstlisting}

\begin{lstlisting}[caption={Delta-based alignment function for lists.},label={lst:align1}]
align :: BiGUL a b
      -> (b -> a)
      -> Delta [b] [b]
      -> BiGUL [a] [b]
align b c d = emb g p
  where g s   = get (align' b c) (s, getId s)
        p s v = fst (put (align' b c) (s, d) v)
\end{lstlisting}
\end{comment}

%%% Generic Implementation for Container/Shapely Types
\subsection{Generic Implementation for Container/Shapely Types}

\noindent\TODO{
\begin{itemize}
  \item A generalization of the implementation for lists.
    \begin{itemize}
      \item This is currently implemented with any container as the source and a
        list as a view.
    \end{itemize}
\end{itemize}
}

%%% Other Matching Algorithms Built Upon Deltas
\subsection{Other Matching Algorithms Built Upon Deltas}

It is possible to make minor changes to the |align| function to
implement other kinds of alignments, e.g., key-based (for the special case of
lists):

%\begin{lstlisting}[caption={Key-based alignment function for lists.},label={lst:keyalign}]
\begin{code}
keyAlign :: (Shapely s, s ~ [], Eq b, Eq k)
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
to infer a delta --- |keyDelta|.

%\begin{lstlisting}[caption={Calculation of deltas using key-based alignment.},label={lst:keydelta}]
\begin{code}
keyDelta :: (Shapely s, Eq k)
  => (a -> k) -> (b -> k) -> s a -> s b -> Delta
keyDelta sk vk ss vs = Set.fromList [ (sp, vp)  |  (s, sp) <- sps
                                                ,  (v, vp) <- vps
                                                ,  sk s == vk v   ]
  where  sps  = zip (data_ ss) (Set.elems $ locs ss)
         vps  = zip (data_ vs) (Set.elems $ locs vs)
\end{code}

%%%
%%% Conclusion
%%%
\section{Conclusion}

\TODO{This section needs some work.}

When developing bidirectional transformations, changing the side from which the
problem is tackled might provide additional power and flexibility. One of the
cases is with the alignment of elements in containers. Alignment is inherent to
the \emph{put} direction, so that one explicitely deals with it when using this
approach.

Other BX frameworks deal with alignment in very specific ways. One example is
the matching lenses framework~\cite{Barbosa2010}, where new concepts are
introduced in order to provide flexibility and power to BXs, but then users are
dependent on the implementation of the alignment strategies by the same
framework. Another example is the delta lenses over inductive
types~\cite{Pacheco2012}, where lenses are also extended in order to cope with
deltas. In both of these examples, the lens framework was extended so that new
concepts could be reasoned about. In this paper, we have shown that, starting
with a core language and without modifying it, it is possible to reason about
new concepts that fall naturely in a different way of thinking.

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
