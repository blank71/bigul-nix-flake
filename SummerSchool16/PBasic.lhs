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

\subsection{Production: Prod}

If we want to putback a product view |(v1,v2)| to a produce source |(s1,s2)|
we can use |bx1 Prod bx2| to use |bx1| to putback |v1| to |s1| and |bx2| to putback |v2| to |s2|.

< Prod :: BiGUL s1 v1 -> BiGUL s2 v2 -> BiGUL (s1,s2) (v1,v2)

For instance, we can combine |Skip| and |Replace| to putback a view of a pair to a source of a pair.
\begin{verbatim}
*Main> put (Skip `Prod` Replace) (5,1) ((),100)
Right (5,100)
\end{verbatim}

We can even deal with more complicated structure by nesting |Prod|:
\begin{verbatim}
*Main> put ((Skip `Prod` Replace) `Prod` Replace) ((5,1),2) (((),100),200)
Right ((5,100),200)
\end{verbatim}

\subsection{Source/View Rearrangement}

\subsection{Case}

\subsection{Composition}

 
\subsection{Utilites}
