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

Here, |get bx| is a function mapping a source to a view, but can possibly fail:
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
\begin{verbatim}
*PBasic> put (Skip square) 10 100
Just 10
\end{verbatim}
It first checks if the view |100| is the square of the source |10|.
If that is the case, the original source is returned.
But if the view is changed, say to |250|,
it should produce |Nothing|:
\begin{verbatim}
*PBasic> put (Skip square) 10 250
Nothing
\end{verbatim}
To see why |put| produces |Nothing|, we may use
|putTrace| instead of |put| to get more information:
\begin{verbatim}
*PBasic> putTrace (Skip square) 10 250
view not determined by the source
\end{verbatim}

Each putback transformation in BiGUL
is equipped with a unique |get| for doing forward transformation.
We can test the |get| behavior as follows:
\begin{verbatim}
*PBasic> get (Skip square) 5
Just 25
\end{verbatim}
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
\begin{verbatim}
*PBasic> put Replace 1 100
Just 100
\end{verbatim}
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
\begin{verbatim}
*PBasic> put (skip1 `Prod` Replace) (5,1) ((),100)
Just (5,100)
\end{verbatim}
Generally, we can use nested |Prod|s to describe a complicated structural mapping:
\begin{verbatim}
*PBasic> put ((skip1 `Prod` Replace) `Prod` Replace)
             ((5,1),2) (((),100),200)
Just ((5,100),200)
\end{verbatim}

\subsection{Source/view rearrangement}

So far, the source and view are of the same structure. What if we
wish to put a view |(v1,v2)| into a source of a different structure,
say |((s0,s1),s2)|, to replace |s1| by |v1| and
|s2| by |v2|? To do that, we need to rearrange the source and view into the same structure, and BiGUL provides a way of 
rearranging either the source or view through a ``simple'' $\lambda$-expression~|e|:

< $(rearrS  (Q( e :: s1  -> s2  ))) :: BiGUL s2  v   -> BiGUL s1  v
< $(rearrV  (Q( e :: v1  -> v2  ))) :: BiGUL s   v2  -> BiGUL s   v1 

The ``simple'' $\lambda$-expression~$e$ should be wrapped inside Template Haskell quasi-quotes |(Q(...))| (written as \texttt{[||} \ldots \texttt{||]} in plain text Haskell).
By ``simple'' we mean that there should be no wildcards~`|_|' in the argument pattern, and that the body can only contain the argument variables and constructors, and must mention all the argument variables.
Returning to the problem of putting a pair into a triple, we may define the following
putback transformation by rearranging the view:
\begin{code}
putPairOverNPair  ::  (Show s0, Show s1, Show s2)
                  =>  BiGUL ((s0,s1),s2) (s1,s2)
putPairOverNPair  =   $(rearrV (Q( \(v1,v2) -> (((),v1),v2) ))) $
                        (skip1 `Prod` Replace) `Prod` Replace
\end{code}

The mechanism of source/view rearrangement enables us to
process algebraic data structures such as
lists and trees. The following example uses the view to
replace the first element of a nonempty source list:
\begin{code}
pHead  ::  Show s => BiGUL [s] s
pHead  =   $(rearrS (Q( \(s:ss) -> (s, ss) )))$
             $(rearrV (Q( \v -> (v, ()) )))$
               skip1 `Prod` Replace
\end{code}
\begin{verbatim}
*PBasic> put pHead [1,2,3,4] 100
Just [100,2,3,4]
\end{verbatim}
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
\begin{verbatim}
*PBasic> put (pNth 3) [1..10] 100
Just [1,2,3,100,5,6,7,8,9,10]
\end{verbatim}
As we know, any putback function in BiGUL is equipped with
a |get| function.
For |pNth|, we can test its |get| behavior
as follows; its corresponding |get| function is actually
the familiar |take| function.
\begin{verbatim}
*PBasic> get (pNth 3) [1..10]
Just 4
\end{verbatim}

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
< Case  [  $(normal   (Q( mainCond1  :: s -> v -> Bool )) (Q(exitCond1 :: s -> Bool )))
<          ==> (bx1 :: BiGUL s v)
<       ,  $(adaptive (Q( mainCond1' :: s -> v -> Bool ))) 
<          ==> (f1 :: s -> v -> s)
<       ,  ...
<       ,  $(normal   (Q( mainCondn  :: s -> v -> Bool )) (Q(exitCondn :: s -> Bool ))) 
<          ==> (bxn :: BiGUL s v)
<       ,  ...
<       ,  $(adaptive (Q( mainCondn' :: s -> v -> Bool ))) 
<          ==> (fn :: s -> v -> s)
<       ]
<    :: BiGUL s v
It contains a sequence of cases, each of which is either |normal| or
|adaptive|. For a normal case, if the main condition is satisfied, a
corresponding putback transformation is applied. For an adaptive
case, if the main condition is satisfied, a function is used to produce
an adapted source from the current source and view before the whole |Case| is rerun,
with the expectation that one of the normal cases will be applicable this time.
Note that if adaptation does not direct execution to a normal case, an error will be reported at runtime.

Note that |$(normal ...)| takes two predicates, which we call
the \emph{main condition} and the \emph{exit condition}. The
predicate for the main condition is very general, and we can use any
function f of type |(s -> v -> Bool)| to examine the source and view. If
the condition is matched, then the BiGUL program after the predicate
is executed. If the condition is not satisfied, the next branch is
tried. The predicate for the exit condition checks the source only. The
exit conditions in different branches should be disjoint (in principle).

As a simple example, consider using the view to update all
the elements in the source list. To do so, we use |Case| to describe a case analysis.
\begin{code}
replaceAll  ::  (Eq s, Show s) => BiGUL [s] s
replaceAll  =
  Case  [  $(normal (Q( \s v -> length s == 1 )) (Q( \s -> length s == 1 )))
           ==>  $(rearrS (Q( \[x] -> x ))) Replace
        ,  $(normal (Q( \s v -> length s > 1 )) (Q( \s -> length s > 1 )))
           ==>  $(rearrS (Q( \(x:xs) -> (x,xs) )))$
                  $(rearrV (Q( \v -> (v, v) )))$
                    Replace `Prod` replaceAll,
        ,  $(adaptive (Q( \s v -> length s == 0 ))) 
           ==> \s v -> [undefined]
        ]
\end{code}
\begin{verbatim}
*PBasic> put replaceAll [] 100
Right [100]
*PBasic> put replaceAll [1..10] 100
Right [100,100,100,100,100,100,100,100,100,100]
\end{verbatim}
Note that instead of using a general function to describe
the main condition or the exit condition, 
we allow to use patterns. The syntax for the normal and the adaptive
cases are:
< $(normalSV (P( sourcePattern )) (P( viewPattern )) (Q( exitCond )))
<   ==> (bx :: BiGUL s v)
< $(adaptiveSV (P( sourcePattern )) (P( viewPattern )))
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
other part of the view, and are not allowed
to be changed. For instance, for the view |(x, x+1)|, the second
component is computed from the first by increasing it by |1|.
To capture this, BiGUL provides

< Dep :: Eq v' => (v->v') -> BiGUL a v -> BiGUL a (v, v')

to describe this intention. We may, for example, define
\begin{code}
replaceAll2 :: BiGUL [Int] (Int,Int)
replaceAll2 = Dep (+1) replaceAll
\end{code}
to replace all elements of the source by the
first component of the view, while the second component
of the view is a derived one that should be one larger than the first one.
\begin{verbatim}
*PBasic> put replaceAll2 [1..10] (100,101)
Just [100,100,100,100,100,100,100,100,100,100]
*PBasic> put replaceAll2 [1..10] (100,200)
Nothing
*PBasic> putTrace replaceAll2 [1..10] (100,200)
second view component not determined by the first
\end{verbatim}
As seen in the last running of |put|, it reports an error because in the view |(100,200)|,
|200| is not one larger than |100|.

\subsection{Composition}

Bidirectional transformations can be composed.

< Compose :: BiGUL a u -> BiGUL u b -> BiGUL a b

As a simple example, we define the following |pHead2| to use
the view to update the first element of the first element of the source.
\begin{code}
pHead2 :: Show a => BiGUL [[a]] a
pHead2 = pHead `Compose` pHead
\end{code}
\begin{verbatim}
*PBasic> put pHead2 [[1,2],[3,4,5],[]] 100
Just [[100,2],[3,4,5],[]]
\end{verbatim}

\subsection{Utilities}

{\tt Generics.BiGUL.Lib} has some useful predefined functions for building putback transformations.
An interesting one is |emb|, which can safely embed a pair of well-behaved
|get| and |put| into BiGUL.
|emb| itself is defined as follows:

< emb :: Eq v => (s -> v) -> (s -> v -> s) -> BiGUL s v
< emb g p = Case
<   [  $(normal (Q( \s v -> g s == v )) (P( _ )))
<      ==> Skip g
<   ,  $(adaptive (Q( \ _ _ -> otherwise )))
<      ==> p
<   ]

As an application of |emb|, we may define the following putback function
to use a sum to update a pair.
\begin{code}
distSum :: BiGUL (Int, Int) Int
distSum = emb g p
  where  g (x,y) = x+y
         p (x,y) v = (v-y,y)
\end{code}
\begin{verbatim}
*PBasic> put distSum (1,2) 100
Right (98,2)
*PBasic> get distSum (1,2)
Right 3
\end{verbatim}

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
