%include lhs2TeX-macros.lhs

\section{Basics}

\ignore{

\begin{code}
{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts, DeriveGeneric, ViewPatterns, ScopedTypeVariables, TemplateHaskell #-}

module PBasic where
import Generics.BiGUL.Error
import Generics.BiGUL.AST
import Generics.BiGUL.Interpreter
import Generics.BiGUL.TH
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
in the source. For each |bx|, we can run it forwardly by calling |get|
and backwardly by calling |put|.

< get bx :: s -> v
< put bx :: s -> v -> s

where |get bx| is a function mapping a source to a view, while |put bx|
accepts an original source and an update view and returns an updated source.

The core of BiGUL consists of only six basic combinators for constructing
bidirectional transformation through development of well-behaved putback
transformations. 

\subsection{Skip}
 
The first one is the simple primitive

< Skip     :: BiGUL s ()

Its putback semantics is to skip any change on the source for the unit view.
One can test this using ghci after loading the test.hs by
\begin{verbatim}
*Main> put Skip 5 ()
Right 5
\end{verbatim}
which means that |Skip| putbacks the unit view |()| on the source |5| and gets the same source |5|. In fact, each well-behaved putback transformation is equipped with a unique |get| for doing forward transformation.
\begin{verbatim}
*Main> get Skip 5
Right ()
\end{verbatim}
It reads that doing forward transformation for |Skip| on the source |5| gives the unit view |()|.

\subsection{Replace}

The second one is

< Replace  :: BiGUL s s

which is to use the view to replace the source:
\begin{verbatim}
*Main> put Replace 1 100
Right 100
\end{verbatim}
which uses the view |100| to replace the source |1| and gets a new source |100|.

\subsection{Product: Prod}

If we want to putback a view pair |(v1,v2)| to a source pair
|(s1,s2)|,
we may write |bx1 Prod bx2|, a product of two putback transformation,
to putback |v1| to |s1| with |bx1| and |v2| to |s2| with |bx2|.

< Prod :: BiGUL s1 v1 -> BiGUL s2 v2 -> BiGUL (s1,s2) (v1,v2)

For instance, we can combine |Skip| and |Replace| to putback a view pair to a source pair.
\begin{verbatim}
*Main> put (Skip `Prod` Replace) (5,1) ((),100)
Right (5,100)
\end{verbatim}
We may deal with more complicated structure using nested |Prod|:
\begin{verbatim}
*Main> put ((Skip `Prod` Replace) `Prod` Replace) ((5,1),2) (((),100),200)
Right ((5,100),200)
\end{verbatim}

\subsection{Source/View Rearrangement}

So far, the source and the view must be of the same structure. What if we
wish to putback a pair view |(v1,v2)| to a complicated source,
say |((s0,s1),s2))|, where we hope to replace |s1| by |v1| and
|s2| by |v2|? BiGUL provide a way of preprocessing of
rearranging either the soruce
or the view through a natural transformation |tau|.

< $(rearrS [| tau :: s1 -> s2 |]) :: BiGUL s2 v -> BiGUL s1 v
< $(rearrV [| tau :: v1 -> v2 |]) :: BiGUL s v2 -> BiGUL s v1 

Returning to the above problem, we can solve it by defining the following
putback transformation
\begin{code}
putPairOverNPair :: BiGUL ((s0,s1),s2) (s1,s2)
putPairOverNPair = $(rearrS [| \((s0,s1),s2) -> (s1,s2) |]) Replace
\end{code}
and have
\begin{verbatim}
*PBasic> put putPairOverNPair ((5,1),2) (100,200)
Right ((5,100),200)
\end{verbatim}
In fact, it is possible to define |putPairOverNPair| by rearranging the view too.
\begin{code}
putPairOverNPair' :: BiGUL ((s0,s1),s2) (s1,s2)
putPairOverNPair' =  $(rearrV [| \(v1,v2) -> (((),v1),v2) |]) $
                       (Skip `Prod` Replace) `Prod` Replace
\end{code}

The machanism of source/view rearrangement makes it possible
to process algebraic data structures such as
lists and trees. The following example describes using view |v| to
replace the first element of a nonempty source.
\begin{code}
pHead :: BiGUL [s] s
pHead = $(rearrS [| \(s:_) -> s |]) Replace
\end{code}
\begin{verbatim}
*PBasic> put pHead [1,2,3,4] 100
Right [100,2,3,4]
\end{verbatim}

We may go further to define a general putback transforamtion 
to replace the |i|th element of a source list with a view |v|.
\begin{code}
pNth :: Int -> BiGUL [s] s
pNth i = if i == 0 then pHead
         else $(rearrS [| \(x:xs) -> (x,xs) |]) $
                 $(rearrV [| \v -> ((), v) |]) $
                    Skip `Prod` pNth (i-1) 
\end{code}
\begin{verbatim}
*PBasic> put (pNth 3) [1..10] 100
Right [1,2,3,100,5,6,7,8,9,10]
\end{verbatim}
Note that any putback function is equipped with a |get| function (which may
be partial). So for |pNth|, the corresponding |get| function is actually
the familiar |take| function.
\begin{verbatim}
*PBasic> get (pNth 3) [1..10]
Right 4
\end{verbatim}

\subsection{Case}

The |Case| combintor is for case analysis. The basic structure is as follows.
\begin{code}
Case  [  $(normal [| cond1 :: s -> v -> Bool |]) (bx1 :: BiGUL s v),
         $(normal [| cond2 :: s -> v -> Bool |]) (bx2 :: BiGUL s v),
         ...,
         $(normal [| condn :: s -> v -> Bool |]) (bxn :: BiGUL s v),
         $(adaptive [| cond1' :: s -> v -> Bool |]) $ (f1 :: s -> v -> s),
         $(adaptive [| cond2' :: s -> v -> Bool |]) $ (f2 :: s -> v -> s),
         ...,
         $(adaptive [| condm' :: s -> v -> Bool |]) $ (fm :: s -> v -> s)
      ]
  :: BiGUL s v
\end{code}
It contains a sequence of cases. For each case, it is either |normal| or
|adaptive|. For the normal case, if the condition is satisfied, a
corresponding putback transformation is applied. For the  adaptive case,
if the condition is satisfied, a function is used to update the source
with the view so that for the next step one of the normal cases can
be applied.

\subsection{Composition}

 
\subsection{Utilites}
