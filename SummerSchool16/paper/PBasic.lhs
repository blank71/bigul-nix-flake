% !TEX root = paper.tex

%include lhs2TeX-macros.lhs

\section{A quick tour of BiGUL}
\label{sec:tour}

\ignore{


\begin{code}
{-# LANGUAGE FlexibleContexts, TemplateHaskell, TypeFamilies #-}

module PBasic where
import Generics.BiGUL
import Generics.BiGUL.Interpreter
import Generics.BiGUL.TH
import Generics.BiGUL.Lib
import Data.List
import Data.Maybe
import Control.Monad.Except
import GHC.Generics
\end{code}

}

Intuitively, we can think of a bidirectional BiGUL program

< bx :: BiGUL s v

as describing how to manipulate a state consisting of
a source component of type~|s| and a view component of type |v|;
the goal is to embed all information in the view to proper places
in the source. For each |bx :: BiGUL s v|, we can run it forwards by calling |get|
and backwards by calling |put|:

< get  bx :: s       -> Maybe v
< put  bx :: s -> v  -> Maybe s

Here, |get bx| is a function mapping a source to a view, which can possibly fail:
it either returns a successfully computed view wrapped in the |Just| constructor of |Maybe|,
or signifies failure by producing the |Nothing| constructor.
On the other hand, |put bx| accepts an original source and uses a view to update it to get an updated source (and might fail as well).

In BiGUL, it suffices for the programmer to write the |put| behavior (i.e.,
how to use a view to update the original source to a new source),
and the (unique) |get| behavior is obtained for free. 
%
The core of BiGUL consists of a small number of primitives and
combinators for constructing well-behaved
bidirectional transformations, which we introduce below.

\subsection{Skip}
 
The first primitive for writing |put| is

< Skip     :: (s->v) -> BiGUL s v

The put behavior of |Skip f| keeps the source unchanged,
provided that the view is computable from the source by~|f|
(while in the get direction, the view is fully computed by
applying function |f| to the source). Consider a simple |put| defined by
|Skip square| where
\begin{code}
square x = x*x
\end{code}
We can test its put behavior as follows:
\begin{alltt}
*PBasic> put (Skip square) 10 100
\eval*{put (Skip square) 10 100}
\end{alltt}
It first checks if the view |100| is the square of the source |10|.
If that is the case, the original source is returned.
But if the view is changed, say to |250|,
it should produce |Nothing|:
\begin{alltt}
*PBasic> put (Skip square) 10 250
\eval*{put (Skip square) 10 250}
\end{alltt}
To see why |put| produces |Nothing|, we may use
|putTrace| instead of |put| to get more information:
\begin{alltt}
*PBasic> putTrace (Skip square) 10 250
\eval*{putTrace (Skip square) 10 250}
\end{alltt}

Each putback transformation in BiGUL
is equipped with a unique |get| for doing forward transformation.
We can test the |get| behavior as follows:
\begin{alltt}
*PBasic> get (Skip square) 5
\eval*{get (Skip square) 5}
\end{alltt}
In prose: doing the forward transformation of |Skip square| on the
source~|5| gives the view~|25|. If |get| fails,
we can also use |getTrace| to see more information about the failure, analogous to |putTrace|.

As a simple exercise, can you see what the following |skip1| does? 
\begin{code}
skip1  ::  BiGUL s ()
skip1  =   Skip (const ())
\end{code}

\subsection{Replace}

The second primitive is

< Replace  :: BiGUL s s

which completely replaces the source with the view. For instance,
\begin{alltt}
*PBasic> put Replace 1 100
\eval*{put Replace 1 100}
\end{alltt}
uses the view |100| to replace the source |1| and gets a new source |100|.

\subsection{Product}

To use a view pair |(v1,v2)| to update a source pair
|(s1,s2)|,
we can write |Prod bx1 bx2| or |bx1 `Prod` bx2|, a product of two putback transformations
|bx1| and |bx2|,
to use |v1| to update |s1| with |bx1| and |v2| to |s2| with |bx2|.

< Prod :: BiGUL s1 v1 -> BiGUL s2 v2 -> BiGUL (s1,s2) (v1,v2)

For instance, we can use |Prod| to combine |Skip| and |Replace| to put a view pair
into a source pair.
\begin{alltt}
*PBasic> put (skip1 `Prod` Replace) (5,1) ((),100)
\eval*{put (skip1 `Prod` Replace) (5,1) ((),100)}
\end{alltt}
Generally, we can use nested |Prod|s to describe a complicated structural mapping:
\begin{alltt}
*PBasic> put ((skip1 `Prod` Replace) `Prod` Replace)
             ((5,1),2) (((),100),200)
\eval*{put ((skip1 `Prod` Replace) `Prod` Replace) ((5,1),2) (((),100),200)}
\end{alltt}

\subsection{Source/view rearrangement}

So far, the source and view are of the same structure. What if we
wish to put a view |(v1,v2)| into a source of a different structure,
say |((s0,s1),s2)|, to replace |s1| by |v1| and
|s2| by |v2|? To do that, we need to rearrange the source and view into the same structure, and BiGUL provides a way of 
rearranging either the source or view through a ``simple'' $\lambda$-expression~|e|:

< $(rearrS  (Q( e :: s1  -> s2  ))) :: BiGUL s2  v   -> BiGUL s1  v
< $(rearrV  (Q( e :: v1  -> v2  ))) :: BiGUL s   v2  -> BiGUL s   v1 

The ``simple'' $\lambda$-expression~$e$ should be wrapped inside Template Haskell quasi-quotes |(Q(...))| (written as \texttt{[||} \ldots \texttt{||]} in plain text Haskell).
By ``simple'' we mean that there should be no wildcards~`|_|' in the argument pattern, and that the body can only contain the argument variables and constructors, and must mention all the argument variables. We will discuss the details later in Section \ref{sec:rearrangement}.
Returning to the problem of putting a pair into a triple, we may define the following
putback transformation
\begin{code}
putPairOverNPair  ::  (Show s0, Show s1, Show s2)
                  =>  BiGUL ((s0,s1),s2) (s1,s2)
putPairOverNPair  =   $(rearrV (Q( \(v1,v2) -> (((),v1),v2) ))) $
                        (skip1 `Prod` Replace) `Prod` Replace
\end{code}
by first rearranging the view |(v1,v2)| to a triple |(((),v1),v2)|
with same structure as the source, and then using
|(skip1 `Prod` Replace) `Prod` Replace| to
put the arranged view |(((),v1),v2)| into the source |((s0,s1),s2)|.
Note that the type context |(Show s0, Show s1, Show s2)| above is
for printing debugging messages by BiGUL.

The mechanism of source/view rearrangement enables us to
process algebraic data structures such as
lists and trees, by mapping an algebraic structure to
the (nested) pair structure. The following example uses the view to
replace the first element of a nonempty source list:
\begin{code}
pHead  ::  Show s => BiGUL [s] s
pHead  =   $(rearrS (Q( \(s:ss) -> (s, ss) )))$
             $(rearrV (Q( \v -> (v, ()) )))$
               Replace `Prod` skip1
\end{code}
It rearranges the source (a nonempty list) to a pair
with its head element |s| and its tail |ss|, and the view
|v| to a pair |(v,())|, so that we can use |v| to replace |s|
and |()| to keep |ss|. 

\begin{alltt}
*PBasic> put pHead [1,2,3,4] 100
\eval*{put pHead [1,2,3,4] 100}
\end{alltt}

What if we wish to define a general putback transformation 
that uses the view to replace the |i|th element of the source list?
We can define it recursively as follows:
\begin{code}
pNth    ::  Show s => Int -> BiGUL [s] s
pNth i  =   if i == 0  then  pHead
                       else  $(rearrS (Q( \(x:xs) -> (x,xs) ))) $
                               $(rearrV (Q( \v -> ((), v) ))) $
                                 skip1 `Prod` pNth (i-1) 
\end{code}
If |i| is |0|, we simply use |pHead| to update the head
element of the source with the view. Otherwise, we do the same arrangements
on the view and the source as we did for |pHead|,
but then keep the head element unchanged and replace 
the |(i-1)|th element of the tail of the source by the view.

\begin{alltt}
*PBasic> put (pNth 3) [1..10] 100
\eval*{put (pNth 3) [1..10] 100}
\end{alltt}

As we know, any putback function in BiGUL is equipped with
a |get| function.
For |pNth|, we can test its |get| behavior
as follows; its corresponding |get| function is actually
the familiar index function |(!!)|.
\begin{alltt}
*PBasic> get (pNth 3) [1..10]
\eval*{get (pNth 3) [1..10]}
\end{alltt}

Both |pHead| and |pNth| contain the programming pattern in which both the source and view are rearranged into a product and then further updates are performed on corresponding components.
This is a ubiquitous pattern in BiGUL, for which we provide a more compact syntax:
< $(update (P(sourcePattern)) (D(viewPattern)) (D(updates)))
The source and view are respectively decomposed using |sourcePattern| and\break |viewPattern| inside the pattern quasi-quotes
|(P(...))| (written as \texttt{[p||} \ldots \texttt{||]} in plain text Haskell), and corresponding elements are updated using the programs provided in the declaration quasi-quote |(D(...))| (\texttt{[d||} \ldots \texttt{||]} in plain text Haskell).
For example, we may describe |(skip1 `Prod` Replace) `Prod` Replace| by
\begin{code}
testUpdate :: (Show a, Show b, Show c) => BiGUL ((a,b),c) (((),b),c)
testUpdate = $(update  (P( ((x,y),z) ))
                       (P( ((x,y),z) ))
                       (D( x = skip1; y = Replace; z = Replace )))
\end{code}
In this concrete example, the three elements of the tuple (in both the source and view) are bound to the variables |x|, |y|, and~|z|, and they are sent to the three
combinators as arguments in the |(D(...))| part. Note that since |skip1| does nothing on its source but checks if its view is |()|,
 we can just match that source element with a wildcard~`|_|' in the source pattern and avoid writing |skip1| in |(D( ... ))|.
\begin{code}
testUpdate'  ::  (Show a, Show b, Show c) => BiGUL ((a,b),c) (((),b),c)
testUpdate'  =   $(update  (P( ((_   , y), z) ))
                           (P( ((()  , y), z) ))
                           (D( y = Replace; z = Replace )))
\end{code}

\subsection{Case}
\label{sec:PBasic.Case}

The |Case| combinator is for case analysis, and the general structure is as follows:
< Case  [  $(normal   (Q( mainCond  :: s -> v -> Bool )) (Q(exitCond :: s -> Bool )))
<          ==> (bx :: BiGUL s v)
<       ,  ...
<       ,  $(adaptive (Q( mainCond :: s -> v -> Bool ))) 
<          ==> (f :: s -> v -> s)
<       ,  ...
<       ]
<    :: BiGUL s v
It contains a sequence of cases, each of which is either |normal| or
|adaptive|. We try the conditions of these cases in order and decide which branch we go into.
\begin{itemize}
\item For a normal case,
|$(normal ...)| takes two predicates, which we call
the \emph{main condition} and the \emph{exit condition}. The
predicate for the main condition is very general, and we can use any
function of type |(s -> v -> Bool)| to examine the source and view.
The predicate for the exit condition checks the source only.
If the main and the exit conditions are satisfied,
then the BiGUL program after the arrow (|==>|) is executed. 
The exit conditions in different branches are expected to be disjoint for efficient
execution of the forward transformation.

\item For an adaptive
case, if the main condition is satisfied, a function of type |(s -> v -> s)|
is used to produce
an adapted source from the current source and view before the whole |Case| is rerun,
with the expectation that one of the normal cases will be applicable this time.
Note that if adaptation does not directly execute to a normal case,
an error will be reported at runtime. 


\end{itemize}

As a simple example, consider using the view to replace each 
element in the source list. To do so, we use |Case| to describe a case analysis.
\begin{code}
replaceAll  ::  (Eq s, Show s) => BiGUL [s] s
replaceAll  =
  Case  [  $(normal (Q( \s v -> length s == 1 )) (Q( \s -> length s == 1 )))
           ==>  $(rearrS (Q( \[x] -> x ))) Replace
        ,  $(normal (Q( \s v -> length s > 1 )) (Q( \s -> length s > 1 )))
           ==>  $(rearrS (Q( \(x:xs) -> (x,xs) )))$
                  $(rearrV (Q( \v -> (v, v) )))$
                    Replace `Prod` replaceAll
        ,  $(adaptive (Q( \s v -> length s == 0 )))
           ==> \s v -> [undefined]
        ]
\end{code}
It consists of two normal cases and one adaptive case.
The first normal case says that if the source is of length |1| (containing a single element),
we rearrange the source list by extracting the single element, and replace this element
with the view.
The second normal case says that if the source has more than |1| element, we 
rearrange the source list to a pair of its head element and its tail, rearrange
the view by duplicating it to a pair, and use one copy of the view to replace the head element, and the other copy to recursively replace each element in the tail of the source.
The last adaptive case says that if the source is empty, we adapt the source
to a singleton list with the \emph{don't-care} element (defined by |undefined|), and rerun the whole
|Case| executing the first normal case. 

\begin{alltt}
*PBasic> put replaceAll [] 100
\eval*{put replaceAll [] 100}
*PBasic> put replaceAll [1..10] 100
\eval*{put replaceAll [1..10] 100}
\end{alltt}
Note that in the first running example, the source |[]| is first adapted to |[undefined]|,
and the \emph{don't care} element |undefined| is replaced by |100| at the rerun of
the whole |Case|.

As another interesting example, we define |emb|, which can safely embed any pair of well-behaved
|get| and |put| into BiGUL. It is defined as follows:

< emb :: Eq v => (s -> v) -> (s -> v -> s) -> BiGUL s v
< emb g p = Case
<   [  $(normal (Q( \s v -> g s == v )) (Q( \s -> True )))
<      ==> Skip g
<   ,  $(adaptive (Q( \ _ _ -> otherwise )))
<      ==> p
<   ]

where, given a pair |(g,p)| of well-behaved |get| and |put| functions,
if the view is the same as that produced by applying |g| to the source, we make no change
on the source with |Skip g| (hinting that the view can be produced using $g$), otherwise we adapt the source using |p| to
reflect the change on the view to the source. Note that if |p| and |g| form a well-behaved bidirectional transformation, in the rerun of the whole |Case| after the adaptation, the first normal case will always be applicable. To see a use of |emb|, we may define the following putback function
to update a pair with its sum.
\begin{code}
pSum2 :: BiGUL (Int, Int) Int
pSum2 = emb g p
  where  g (x,y) = x+y
         p (x,y) v = (v-y,y)
\end{code}
%\begin{alltt}
%*PBasic> put pSum2 (1,2) 100
%\eval{put pSum2 (1,2) 100}
%*PBasic> get pSum2 (1,2)
%\eval{get pSum2 (1,2)}
%\end{alltt}



While we allow a general function to describe
the main condition or the exit condition, 
it is usually more concise to use patterns to describe these conditions.
For instance, we may replace the condition |(Q( \s -> length s == 1 ))| by
\begin{spec}
(Q( \[x] -> True ))
\end{spec}
Here, the meaning of a boolean-valued pattern-matching
lambda-expression is redefined as a total function which computes to
|False| when an input does not match the pattern; this meaning is
different from that of a general pattern-matching lambda-expression,
which fails to compute when the pattern is not matched.
For example,
in general the lambda-expression |\[x] -> True| will fail
to compute if the first input is not a singleton list; when used in branch
construction, however, the lambda-expression will compute to |False|
upon encountering an empty list.
A unary condition like |(Q( \[x] -> True ))| where only the pattern part matters can be abbreviated to
\begin{spec}
(P( [x] ))
\end{spec}
to further reduce syntactic noise.
Finally, to also allow this kind of abbreviation in main conditions, BiGUL provides 
a special form for the |normal| case where the main condition is specified as the conjunction of two unary predicates on the source and view respectively:
< $(normalSV   (Q( sourceCond :: s -> Bool ))
<              (Q( viewCond :: v -> Bool ))
<              (Q( exitCond :: s -> Bool )))
<   ==> (bx :: BiGUL s v)
and a special form for the |adaptive| case where the main condition is specified as the conjunction of two unary predicates on the source and view respectively:
< $(adaptiveSV  (Q( sourceCond :: s -> Bool ))
<               (Q( viewCond :: v -> Bool )))
<   ==> (f :: s -> v -> s)


\ignore{
\begin{code}
repHead :: BiGUL [Int] Int
repHead = Case [
  $(normal (Q( \s v -> length s > 0 )) (Q( \s -> length s > 0 )))
    ==> $(rearrS (Q( \(x:xs) -> x ))) Replace,
  $(adaptive (Q( \s v -> length s == 0 )))
    ==> \s v -> [0]
 ]
\end{code}
}


\subsection{View dependency}

Sometimes, a view may contain derived values that are computed from
other parts of the view, and the view should be consistently changed.
For instance, for the view |(x, even(x))|, the second
component is an indicator showing whether or not the first component is an even number.
To capture this, BiGUL provides

< Dep :: Eq v' => (v->v') -> BiGUL a v -> BiGUL a (v, v')

to describe this intention. We may, for example, define
\begin{code}
replaceAll2 :: BiGUL [Int] (Int,Bool)
replaceAll2 = Dep even replaceAll
\end{code}
to replace all elements of the source by the
first component of the view, while checking whether
the second component is consistent with the first component.
\begin{alltt}
*PBasic> put replaceAll2 [1..10] (100,True)
\eval*{put replaceAll2 [1..10] (100,True)}
*PBasic> put replaceAll2 [1..10] (100,False)
\eval*{put replaceAll2 [1..10] (100,False)}
*PBasic> putTrace replaceAll2 [1..10] (100,False)
\eval*{putTrace replaceAll2 [1..10] (100,False)}
\end{alltt}
As seen in the last running of |put|, it reports an error because the view |(100,False)|
is inconsistent: |100| is an even number, so the second component should be |True|.

\subsection{Composition}

As in the get-based bidirectional programming,
putback-based bidirectional transformations
can be composed similarly:

< Compose :: BiGUL a u -> BiGUL u b -> BiGUL a b

where we can put the view |b| to the source |a| through the intermediate data |u|, by
composing the putback function from |b| to |u| and that from |u| to |a|.

As a simple example, consider that we wish to use the view to update
the head element of the head element of a list of lists.
We can define such putback function as the following |pHead2|
by composing |pHead| with |pHead|.
\begin{code}
pHead2 :: Show a => BiGUL [[a]] a
pHead2 = pHead `Compose` pHead
\end{code}
The following is a running example.
\begin{alltt}
*PBasic> put pHead2 [[1,2],[3,4,5],[]] 100
\eval*{put pHead2 [[1,2],[3,4,5],[]] 100}
\end{alltt}

%\subsection{Utilities}

%{\tt Generics.BiGUL.Lib} has some useful predefined functions for building putback transformations.

\ignore{
\begin{code}
pHead' :: Show s
       => BiGUL [s] s
pHead' = Case [
     $(normal (Q( \s v -> not (null s) )) (Q( not . null )))
       ==> pHead,
     $(adaptive (Q( \s v -> null s )))
       ==> \s v -> [v]
     ]


pEither :: (Show a, Show b, Eq a)
        => a -> BiGUL (Either a b) a
pEither x0 = Case [
  $(normalSV (P( Left _ )) (P( _ )) (P( Left _ )))
    ==> $(update (P( Left x )) (P( x )) (D( x = Replace ))),
  $(normalSV (P( Right y )) (Q( \x -> x==x0 )) (P( Right _ )))
    ==> Skip (const x0),
  $(adaptive (Q( \ _ _ -> True )))
    ==> \s v -> Left v
  ]

\end{code}
}
