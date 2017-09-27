% !TEX root = tutorial.tex

%include lhs2TeX-macros.lhs

\section{Bidirectional programming on lists}
\label{sec:lists}

\ignore{

\begin{code}
{-# LANGUAGE FlexibleContexts, TemplateHaskell, TypeFamilies #-}

module List where

import Generics.BiGUL
import Generics.BiGUL.Interpreter
import Generics.BiGUL.TH
import Generics.BiGUL.Lib
import Data.List
import Data.Maybe
import Control.Monad.Except
import GHC.Generics

import Basic
\end{code}

}

To give some more involved examples, in this section we demonstrate that
many list functions can be bidirectionalized
using BiGUL.
The putback behaviors of these functions are in fact non-trivial, and the reader might want to skip to later sections in which more examples are developed, starting from \autoref{sec:alignment}.

To show the correspondence with the original list functions, we prefix
the original forward function names with \emph{lens}. Note that in our context,
the original forward
functions can be automatically derived from the new putback transformations
by calling |get|.

We shall focus on bidirectionalizing |foldr|, an important higher-order function on lists:

< foldr :: (a -> b -> b) -> b -> [a] -> b
< foldr f e []      = e
< foldr f e (x:xs)  = f x (foldr f e xs)

Many interesting functions can be defined in terms of |foldr|:
< sum        = foldr (+) 0
< map f      = foldr (\a r -> f a : r) []
where |sum| sums up all the elements in a list, and |map f| applies |f| to
every element in a list.
%< filter p   = foldr (\a r -> if p a then a : r else r) []
%< reverse p  = foldr (\a r -> r ++ [a]) []
%< sort       = foldr insert []

We start by developing a putback function for |foldr| in BiGUL:
\begin{code}
lensFoldr  ::  (Show a, Show v)
           =>  BiGUL (a, v) v -> (v->Bool) -> BiGUL ([a], v) v
\end{code}
where we hope to define a putback program of type |BiGUL ([a], v) v|
that is to use the view to update the source,
a list together with a value, by recursively applying
a simpler putback function of type |BiGUL (a, v) v|
(until a condition is satisfied or all the list elements have been visited).
The program is somewhat tricky, and is probably not easy to understand since |Compose| is involved.
\begin{code}
lensFoldr bx pv =
  Case  [   $(adaptive (Q( \(x,y) v -> pv v && length x /= 0 )))
            ==> \(x,y) v -> ([],y)
        ,   $(normal (Q( \(xs,_) v -> null xs )) (Q( \(xs,_) -> null xs )))
            ==>  $(rearrV (Q( \v -> ((),v) ))) $
                   $(update (P( (_, v) )) (P( ((),v ) )) (D( v = Replace )))
        ,   $(normalSV (P( _ )) (P( _ )) (Q( \(xs,_) -> not (null xs) )))
            ==>  $(rearrS (Q( \((x:xs), e) -> (x, (xs,e))  )))$
                   (Replace `Prod` lensFoldr bx pv) `Compose` bx
        ]
\end{code}
The |lensFoldr| program accepts a putback function |bx| and a
view condition |pv|, and performs a case analysis to put the view |v|
to the source |(xs,e)|. If the view |v| satisfies |pv|
but the list |xs| in the source is not empty, then it adapts the list to be empty.
If the list |xs| in the source
is empty, we do nothing but use the view to replace the second component of the source.
Otherwise, we rearrange the source from the form of |(x:xs,e)| to that of |(x,(xs,e))|, and
apply |lensFoldr| recursively with a composition with |bx|. One may understand the composition
through the following picture (where | r = Replace `Prod` lensFoldr bx pv|).
\[
(x,(xs,e)) \overset{r}{\leftrightarrow} (x,e')
\overset{bx}{\leftrightarrow} v
\]

With |lensFoldr|, we can redefine many list functions from the putback point
of view. As the first example, consider |mapAppend|:
< mapAppend f (xs,ys) = map f xs ++ ys
We can define its putback function as follows.

\begin{code}
lensMapAppend :: (Show a, Show b) => BiGUL a b -> BiGUL ([a],[b]) [b]
lensMapAppend pf =  lensFoldr bx null
   where  bx =  $(rearrV (Q( \(v:vs) -> (v,vs) ))) $
                    pf `Prod` Replace
\end{code}
Here |bx| has the type of |BiGUL (a,[b]) [b]| and
is defined on |pf| that has the type of |BiGUL a b|.

\begin{lstlisting}
*List> put (lensMapAppend dec1) ([0..10],[]) [100..110]
\eval*{put (lensMapAppend dec1) ([0..10],[]) [100..110]}
*List> get (lensMapAppend dec1) ([1..10],[])
\eval*{get (lensMapAppend dec1) ([1..10],[])}
\end{lstlisting}
Note that, for testing, we embed into our framework
the bijective functions for increasing and decreasing a number by~|1|.
\begin{code}
dec1  ::  (Eq a, Num a) => BiGUL a a
dec1  =   emb g p
  where  g s    = s+1
         p s v  = v-1
\end{code}

\ignore{
The second example is to bidirectionalize |reverse|, which is to reverse the
elements of a list.
\begin{code}
lensReverse :: Show a => BiGUL [a] [a]
lensReverse =
  Case  [  $(adaptive (Q( \s v -> length s < length v )))
           ==> \s v -> v
        ,  $(normalSV (P( _ )) (P( _ )) (Q( \ s -> True )))
           ==>  $(rearrS (Q( \s -> (s,[]) ))) $
                  lensFoldr (lensSwap `Compose` lensSnoc) null
        ]
\end{code}
When the source is shorter than the view, we add more elements to the source
by filling in it with the elements of the view (Note that this is one option;
we could do other ways by, say, duplicating elements in the source). When the source is long enough, we decompose the view into a snoc-list using |lensSnoc|, and use it
to update the cons-list of the source.
\begin{code}
lensSnoc  ::  Show a => BiGUL ([a],a) [a]
lensSnoc  =
  Case  [  $(normal (Q( \s v -> length v == 1 )) (Q( \(s,_) -> null s )))
           ==> $(rearrV (Q( \[v] -> ([],v) ))) Replace
        ,  $(normal (Q( \(s,_) v -> length s > 0 )) (Q( \(s,_) -> length s > 0 )))
           ==> $(rearrS (Q( \(y:ys,x) -> (y,(ys,x)) ))) $
                 $(rearrV (Q( \(v:vs) -> (v,vs) ))) $
                   Replace `Prod` lensSnoc
        ,  $(adaptive (Q( \(s,_) v -> null s )))
           ==> \(s,x) _ -> ([undefined], x)
        ]

lensSwap  ::  (Show a, Show b) => BiGUL (a,b) (b,a)
lensSwap  =   $(rearrS (Q( \(x,y) -> (y,x) ))) Replace
\end{code}

Below are some testing examples.
\begin{lstlisting}
*List> put lensSnoc ([2,3,4],1) [10,11,12,13]
\eval*{put lensSnoc ([2,3,4],1) [10,11,12,13]}
*List> put lensSnoc ([2,3,4],1) [10,11,12,13,14]
\eval*{put lensSnoc ([2,3,4],1) [10,11,12,13,14]}
*List> put lensSnoc ([2,3,4],1) [10,11]
\eval*{put lensSnoc ([2,3,4],1) [10,11]}
*List> get lensSnoc ([1..10], 100)
\eval*{get lensSnoc ([1..10], 100)}

*List> put lensReverse [1..10] [100..105]
\eval*{put lensReverse [1..10] [100..105]}
*List> put lensReverse [1..10] [100..115]
\eval*{put lensReverse [1..10] [100..115]}
*List> get lensReverse [1..10]
\eval*{get lensReverse [1..10]}
\end{lstlisting}

}

For a second example, consider the function |sum (xs,e)|, which is to sum up
all elements of the list |xs| starting from the seed |e|. If the sum is changed,
there are many ways to reflect this change to the input |(xs,e)|. The following
describes one way in BiGUL:
\begin{code}
lensSum  ::  BiGUL ([Int], Int) Int
lensSum  =   lensFoldr pSum2 (const False)
\end{code}
which will reflect the change difference on the view to the head element of |xs|
if |xs| is not empty, or to the seed |e| otherwise. We may choose other ways, say to
reflect the change difference on the view only to the seed by defining
\begin{code}
lensSum'  ::  BiGUL ([Int], Int) Int
lensSum'  =   lensFoldr ($(rearrS (Q( \(x,y) -> (y,x) ))) pSum2) (const False)
\end{code}
Note that although |get lensSum ([1,2,3],0) = get lensSum' ([1,2,3],0) =| \eval{get lensSum' ([1,2,3],0)}, their putback behaviors are different:
\begin{align*}
& |put|\;\mathrlap{|lensSum|}\phantom{|lensSum'|}\;|([1,2,3],0) 16| = \eval{put lensSum ([1,2,3],0) 16} \\
& |put lensSum' ([1,2,3],0) 16| = \eval{put lensSum'  ([1,2,3],0) 16}
\end{align*}

It is worth noting that our definition of |lensFoldr| is just one
putback function for |foldr|, and there are many others.
This reflects the fact
that one |foldr| can have many |put|s, each describing one
updating strategy.
