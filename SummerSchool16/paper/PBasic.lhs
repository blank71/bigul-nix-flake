%include lhs2TeX-macros.lhs

\section{A quick tour of BiGUL}

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
in the source. For each |bx :: BiGUL s v|, we can run it forwardly by calling |get|
and backwardly by calling |put|.

< get bx :: s -> Maybe v
< put bx :: s -> v -> Maybe s

Here, |get bx| is a function mapping a source to a view if it succeeds,
while |put bx|
accepts an original source and uses a view to update it to get an updated source.

In BiGUL, it suffices for users to write the |put| behavior (i.e.,
how to use a view to update the original source to a new source),
and the (unique) |get| behavior is obtained for free. 
%
The core of BiGUL consists of a small number of primitives and
combinators for constructing valid (well-behaved)
bidirectional transformations.

\subsection{Skip}
 
The first primitive for writing |put| is

< Skip     :: (s->v) -> BiGUL s v

The put behavior of |Skip f| forbits any change on the view
and thus skips any change on the source
(while in the get direction, the view is fully computed by
applying function |f| to the source). Consider a simple |put| defined by
|Skip square| where
\begin{code}
square x = x*x
\end{code}
we can test its put behavior as follows:
\begin{verbatim}
*Main> put (Skip square) 10 100
Just 10
\end{verbatim}
It first checks if the view |100| is the square of the source |10|, and returns
the original source if it is. But if the view is changed, say to |250|,
it should return |Nothing|:
\begin{verbatim}
*Main> put (Skip square) 10 250
Nothing
\end{verbatim}
If one wants to see why |put| returns |Nothing|, he may use
|putTrace| instead of |put| to get more information.
\begin{verbatim}
*Main> putTrace (Skip square) 10 250
view not determined by the source
\end{verbatim}

Note that each well-behaved putback transformation in BiGUL
is equipped with a unique |get| for doing forward transformation.
We can test the |get| behavior as follows.
\begin{verbatim}
*Main> get (Skip square) 5
Just 25
\end{verbatim}
It reads that doing forward transformation for |Skip square| on the
source of |5| gives the view of |25|. Like that we have |putTrace| for |put|
to see more execution information about |put|,
we have |getTrace| for |get| to see  more execution information about |get|.

As a simple exercise, can you see what the following |skip1| is? 
\begin{code}
skip1 :: BiGUL s ()
skip1 = Skip (const ())
\end{code}

\subsection{Replace}

The second primitive is

< Replace  :: BiGUL s s

which is to use the view to completely replace the source. For instance,
\begin{verbatim}
*Main> put Replace 1 100
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

For instance, we can use |Prod| to combine |Skip| and |Replace| to putback a view pair
to a source pair.
\begin{verbatim}
*Main> put (skip1 `Prod` Replace) (5,1) ((),100)
Just (5,100)
\end{verbatim}
Genrally, we can use nested |Prod|s to deal with a complicated structural mapping:
\begin{verbatim}
*Main> put ((skip1 `Prod` Replace) `Prod` Replace)
           ((5,1),2) (((),100),200)
Just ((5,100),200)
\end{verbatim}

To help describe structural mapping more directly, we provide the following
syntactic sugar:
< $(update  [p| sourcePattern |]
<           [p| viewPattern |]
<           [d| updatingStrategy |])
Both the Source and the view are decomposed by the patterns in the
|[p|| ... ||]| and corresponding elements are updated based on the
updating strategy described in the |[d|| ... ||]|.
As an example, we may describe |(skip1 `Prod` Replace) `Prod` Replace| by
\begin{code}
testUpdate ::  (Show a, Show b, Show c) =>
               BiGUL ((a,b),c) (((),b),c)
testUpdate = $(update  [p| ((x,y),z) |]
                       [p| ((x,y),z) |]
                       [d| x = skip1; y = Replace; z = Replace |])
\end{code}
In this concrete example, the three elements of the tuple (both in the source and in the view) are bound to variables |x,y,z|, and they are sent to the three
combinators as arguments in the |[d|| ... ||]| part. Note that since |skip1| does nothing on the source but checks if the view is |()|,
 we could just mark the source element as underline(\_) in |[p|| sourcePattern ||]| and avoid writing |skip1| in |[d|| ... ||]|.
\begin{code}
testUpdate' ::  (Show a, Show b, Show c) =>
                BiGUL ((a,b),c) (((),b),c)
testUpdate' = $(update  [p| ((_,y),z) |]
                        [p| (((),y),z) |]
                        [d| y = Replace; z = Replace |])
\end{code}

\subsection{Source/View rearrangement}

So far, the source and the view are of the same structure. What if we
wish to putback a view |(v1,v2)| to a source of a different structure,
say |((s0,s1),s2))|, to replace |s1| by |v1| and
|s2| by |v2|? BiGUL provides a way of 
rearranging either the source
or the view through a natural transformation |tau| to make both the view and
the source have the same structure.

< $(rearrS [| tau :: s1 -> s2 |]) :: BiGUL s2 v -> BiGUL s1 v
< $(rearrV [| tau :: v1 -> v2 |]) :: BiGUL s v2 -> BiGUL s v1 

Returning to the above problem, we may define the following
putback transformation by rearranging the source
\begin{code}
putPairOverNPair ::  (Show s1, Show s2) =>
                     BiGUL ((s0,s1),s2) (s1,s2)
putPairOverNPair = $(rearrS [| \((s0,s1),s2) -> (s1,s2) |]) Replace
\end{code}
and have
\begin{verbatim}
*PBasic> put putPairOverNPair ((5,1),2) (100,200)
Just ((5,100),200)
\end{verbatim}
Or we may define it by rearranging the view:
\begin{code}
putPairOverNPair' ::  (Show s0, Show s1, Show s2) =>
                      BiGUL ((s0,s1),s2) (s1,s2)
putPairOverNPair' =  $(rearrV [| \(v1,v2) -> (((),v1),v2) |]) $
                       (skip1 `Prod` Replace) `Prod` Replace
\end{code}

The mechanism of source/view rearrangement enables us to
process algebraic data structures such as
lists and trees. The following example uses view |v| to
replace the first element of a nonempty source list.
\begin{code}
pHead :: Show s => BiGUL [s] s
pHead = $(rearrS [| \(s:_) -> s |]) Replace
\end{code}
\begin{verbatim}
*PBasic> put pHead [1,2,3,4] 100
Just [100,2,3,4]
\end{verbatim}
What if we wish to define a general putback transformation 
that uses the view to replace the |i|th element of the source list?
We can define it recursively as follows.
\begin{code}
pNth :: Show s => Int -> BiGUL [s] s
pNth i =  if i == 0 then pHead
          else  $(rearrS [| \(x:xs) -> (x,xs) |]) $
                   $(rearrV [| \v -> ((), v) |]) $
                      skip1 `Prod` pNth (i-1) 
\end{code}
\begin{verbatim}
*PBasic> put (pNth 3) [1..10] 100
Just [1,2,3,100,5,6,7,8,9,10]
\end{verbatim}
As we know that any putback function in BiGUL is equipped with
a |get| function, for |pNth|, we can test its |get| behavior
as follows; its corresponding |get| function is actually
our familiar |take| function.
\begin{verbatim}
*PBasic> get (pNth 3) [1..10]
Just 4
\end{verbatim}

\subsection{Case}
\label{sec:PBasic.Case}

The |Case| combinator is for case analysis, which is very useful.
The general structure is as follows.
< Case  [  $(normal   [| enteringCond1  :: s -> v -> Bool |] [|exitCond1 :: s -> Bool |])
<            ==> (bx1 :: BiGUL s v)
<       ,  $(adaptive [| enteringCond1' :: s -> v -> Bool |]) 
<            ==> (f1 :: s -> v -> s)
<       ,  ...
<       ,  $(normal   [| enteringCondn  :: s -> v -> Bool |] [|exitCond1 :: s -> Bool |]) 
<            ==> (bxn :: BiGUL s v)
<       ,  ...
<       ,  $(adaptive [| enteringCondm' :: s -> v -> Bool |]) 
<            ==> (fm :: s -> v -> s)
<       ]
<    :: BiGUL s v
It contains a sequence of cases. For each case, it is either normal or
adaptive. For the normal case, if the condition is satisfied, a
corresponding putback transformation is applied. For the adaptive
case, if the condition is satisfied, a function is used to update the
source with the view so that for the next step one of the normal cases
can be applied. Note that if adaptation does not lead the source and
the view to a normal case, an error will be reported at runtime.

Note that |$(normal ... ...)| takes two predicates. The first one is
the entering-condition while the second one is the exit-condition. The
predicate for entering-condition is very general, and we can use any
function f of type |(s -> v -> Bool)| to examine the source and view. If
the condition is matched, then the BiGUL program after the predicate
is executed. If the condition is not satisfied, the next branch is
tried. The predicate for exit-condition checks the source only. The
exit-condition in different branches should NOT be overlapped.

As a simple example, consider using the view to update all
the elements in the source list. To do so, we use |Case|.
\begin{code}
replaceAll :: (Eq s, Show s) => BiGUL [s] s
replaceAll =
  Case  [
           $(normal [| \s v -> length s == 1 |] [| \s -> length s == 1 |])
             ==> $(rearrS [| \[x] -> x |]) Replace,
           $(normal [| \s v -> length s > 1 |] [| \s -> length s > 1 |])
             ==> $(rearrS [| \(x:xs) -> (x,xs) |]) $
                    $(rearrV [| \v -> (v, v) |]) $
                       Replace `Prod` replaceAll,
           $(adaptive [| \s v -> length s == 0 |]) 
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
the entering condition or the exit condition, 
we allow to use patterns. The syntax for the normal and the adaptive
cases are:
< $(normalSV [p| sourcePattern |] [p| viewPattern |] [| exitCond |])
<   ==> (bx :: BiGUL s v)
< $(adaptiveSV [p| sourcePattern |] [p| viewPattern |])
<   ==> (fm :: s -> v -> s)

\ignore{
\begin{code}
repHead :: BiGUL [Int] Int
repHead = Case [
  $(normal [| \s v -> length s > 0 |] [| \s -> length s > 0 |])
    ==> $(rearrS [| \(x:xs) -> x |]) Replace,
  $(adaptive [| \s v -> length s == 0 |])
    ==> \s v -> [0]
 ]
\end{code}
}

\subsection{View dependency}

Sometimes, a view may contain derived value that is computed from
other part of the view and not allowed
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
of the view is a derived one that should be one bigger than the first one.
\begin{verbatim}
*PBasic> put replaceAll2 [1..10] (100,101)
Just [100,100,100,100,100,100,100,100,100,100]
*PBasic> put replaceAll2 [1..10] (100,200)
Nothing
*PBasic> putTrace replaceAll2 [1..10] (100,200)
second view component not determined by the first
\end{verbatim}
As seen in the last running of |put|, it reports an error because in the view |(100,200)|,
|200| is not one bigger than |100|.

\subsection{Composition}

Putback transformations can be composed.

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

{\tt Generics.BiGUL.Lib} has predefined some useful functions for building putback transformations.
One interesting one is |emb| that can safely embed a pair of well-behaved
|get| and |put| into a putback transformation in our context.
|emb| itself is defined as follows.

< emb :: Eq v => (s -> v) -> (s -> v -> s) -> BiGUL s v
< emb g p = Case
<   [ $(normal [| \s v -> g s == v |] [p| _ |])
<     ==> Skip g
<   , $(adaptive [| \s v -> {- g s /= v -} True |])
<     ==> p
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
     $(normal [| \s v -> not (null s) |] [| not . null |])
       ==> pHead,
     $(adaptive [| \s v -> null s |])
       ==> \s v -> [v]
     ]


pEither :: (Show a, Show b, Eq a)
        => a -> BiGUL (Either a b) a
pEither x0 = Case [
  $(normalSV [p| Left _ |] [p| _ |] [p| Left _ |])
    ==> $(update [p| Left x |] [p| x |] [d| x = Replace |]),
  $(normalSV [p| Right y |] [| \x -> x==x0 |] [p| Right _ |])
    ==> Skip (const x0),
  $(adaptive [| \ _ _ -> True |])
    ==> \s v -> Left v
  ]

\end{code}
}
