% !TEX root = tutorial.tex

%include lhs2TeX-macros.lhs

\section{Bidirectionalizing relational queries with BiGUL\protect\footnote{%
The text of this section is adapted from our BX~2016 paper~\cite{ZanLKH16}.}}
\label{sec:Brul}

\ignore{

\begin{code}
{-# LANGUAGE FlexibleContexts, TemplateHaskell, TypeFamilies, ScopedTypeVariables #-}

module Brul where
import Generics.BiGUL
import Generics.BiGUL.Interpreter
import Generics.BiGUL.TH
import Generics.BiGUL.Lib

import GHC.Generics
import Data.List
import Control.Monad.Except
import qualified Data.Map as Map
import Data.Maybe

import Alignment (employees,bx,updatedEmployees0,cr)

\end{code}

}

In work on relational databases, the view-update problem is about how
to translate update operations on the view table to corresponding
update operations on the source table properly. Relational
lenses \cite{Bohannon:06} try to solve this
problem by providing a list of combinators that let the user write get
functions (queries) with specified updated policies for put functions
(updates); however this can only provide limited control of update
policies. To resolve this problem, we define a new library \textsc{Brul} \cite{ZanLKH16},
where two \emph{putback}-based combinators (operators) are designed
to specify update policies, from which forward queries (selection, projection, join)
can be automatically derived.
\begin{itemize}
\item |align| is to update a source list with a view list by aligning part of source elements filtered by a predicate with view elements according to a matching criteria between source element and view element;
%
\item |unjoin| is to decompose a join view to update two sources.
\end{itemize}

In this section, we will focus on |align|. As will be seen in Section
\ref{sec:policy}, it can describe more flexible update strategies
(related to selection/projection queries) than relational lenses,
while the well-behavedness is guaranteed for free.

\subsection{Relational database representation}
\label{sec:table}

A relational table (|RT|) is denoted by a list of records (where the order
does not really matter),
and each record (|Record|) is denoted by a list of attributes of type |RType|, which could
be an integer, a string, a floating point number, or a double-precision floating point number.
\begin{code}
type RT      =  [Record]
type Record  =  [RType]
data RType   =  RInt Int
             |  RString String
             |  RFloat Float
             |  RDouble Double
             deriving (Show, Eq, Ord)
\end{code}
To allow pattern matching on the newly defined algebraic data type |RType| in BiGUL, we need to add the following declaration.
\begin{align*}
& |deriveBiGULGeneric|\;\texttt{\char13\char13}|RType|
\end{align*}
\ignore{\begin{code}
deriveBiGULGeneric  ''RType
\end{code}}

\ignore{

\begin{code}
showRType :: RType -> String
showRType (RInt i)       = show i
showRType (RString str)  = str
showRType (RFloat f)     = show f
showRType (RDouble d)    = show d

tshow :: [Record] -> String
tshow [] = ""
tshow (line: ls) = tshow1 line ++ "\n" ++ tshow ls

tshow1 :: Record -> String
tshow1 [] = ""
tshow1 (r: rs) = showRType r ++ ", " ++ tshow1 rs

showTable :: [Record] -> IO ()
showTable t = putStr (tshow t)

showResult (Right t) = showTable t
showResult (Left error) = putStrLn (show error)

showTuple :: ([Record], [Record]) -> IO ()
showTuple (s1, s2) = putStrLn "s1:" >>
                     showTable s1 >>
                     putStrLn "\ns2:" >>
                     showTable s2

showResultTuple (Right t) = showTuple t
showResultTuple (Left error) = putStrLn (show error)
\end{code}
}

Consider the table in Figure~\ref{example:s} that
stores five music track records, and each record contains its Track
name, release Date, Rating, Album, and the Quantity of this Album.
We can represent it as follows, where all the records have the same structure.
\begin{code}
s  =  [ [RString "Lullaby"   , RInt 1989, RInt 3, RString "Galore"  , RInt 1]
      , [RString "Lullaby"   , RInt 1989, RInt 3, RString "Show"    , RInt 3]
      , [RString "Lovesong"  , RInt 1989, RInt 5, RString "Galore"  , RInt 1]
      , [RString "Lovesong"  , RInt 1989, RInt 5, RString "Paris"   , RInt 4]
      , [RString "Trust"     , RInt 1992, RInt 4, RString "Wish"    , RInt 5]
      ]
\end{code}


\begin{figure}[t]
\centering
\begin{tabular}{c c c c c}
\hline
Track & Date & Rating & Album & Quantity \\
\hline
Lullaby   &  1989 & 3 &  Galore & 2  \\
Lullaby   &  1989 & 3 &  Show   & 3  \\
Lovesong  &  1989 & 5 &  Galore & 2  \\
Lovesong  &  1989 & 5 &  Paris  & 4  \\
Trust     &  1992 & 4 &  Wish   & 5  \\
\hline
\end{tabular}
\caption{Source table}
\label{example:s}
\end{figure}

\subsection{Relation Alignment}

The alignment of two relational tables, which is related by a selection/projection query, is similar to the key-based list alignment
in Section \ref{sec:alignment}. The difference is that we need to consider
filtering on (i.e., selection of) the source records based on a condition.
%and maintaining of functional dependency
%on the source elements when updates on the view happen.

Let us see how to extend |keyAlign| (in Section \ref{sec:alignment})
to implement the new align |pAlign| that can deal with filtering of source elements.
We extend |keyAlign| with two new arguments; one is
the predicate |p| for filtering source elements,
and the other is the function |h| for hiding/concealing source elements
if their corresponding
elements are removed from the view.
As seen below, |pAlign| has a similar case structure
as that of |keyAlign|, except that we refine the third case of |keyAlign|
into two cases (the third and the fourth cases of |pAlign|): the third case
says that if the view |v| is empty but the first record in the source satisfies |p|,
we should hide this record using |h|, and the fourth case says that
if the first record of the source does not satisfy |p|, we simply ignore it and
continue with the remaining records.

\begin{code}
pAlign  ::  forall s v k DOT (Show s, Show v, Eq k)
        =>  (s -> Bool) -- predicate
        ->  (s -> k) -> (v -> k) -> BiGUL s v -> (v -> s)
        ->  (s -> Maybe s) -- conceal function
        ->  BiGUL [s] [v]
pAlign p ks kv b c h = Case
  [ $(normalSV (P( [] )) (P( [] )) (P( [] )))
    ==> $(update (P( [] )) (P( [] )) (D( )))
  , $(normal (Q( \(s:ss) (v:vs) -> p s && ks s == kv v )) (Q( \(s:ss) -> p s )))
    ==> $(update (P( x:xs )) (P( x:xs )) (D( x = b; xs = pAlign p ks kv b c h )))
  , $(adaptive (Q( \(s:ss) v -> p s && null v)))
    ==> \(s:ss) v -> maybe [] (:[]) (h s) ++ ss
  , $(normal (Q( \(s:ss) v -> not (p s) )) (Q( \(s:ss) -> not (p s) )))
    ==> $(update (P( _:xs )) (P( xs )) (D( xs = pAlign p ks kv b c h )))
  , $(adaptive (Q( \ss (v:vs) -> kv v `elem` map ks (filter p ss) )))
    ==> \ss (v:_) -> uncurry (:) (extract (kv v) ss)
  , $(adaptiveSV (P( _ )) (P( _:_ )))
    ==> \ss (v:_) -> filterCheck p (c v) : ss
  ]
  where
    extract :: k -> [s] -> (s, [s])
    extract k (x:xs)  | p x && ks x == k  = (x, xs)
                      | otherwise         =  let  (y, ys) = extract k xs
                                             in   (y, x:ys)
    filterCheck p v  | p v        = v
                     | otherwise  = error "error in filter checking"
\end{code}

To test, recall the example in Section \ref{sec:alignment}.
Consider the following use of |pAlign|, denoting that the view is selected
from those records from the source whose salary is greater than |1000|, and that
if a view record is removed, the corresponding record in the source will be removed (and thus hidden).
\begin{code}
pSelProj = pAlign (\(k,(n,s)) -> s > 1000) fst fst bx cr' (const Nothing)
  where cr' (k,n) = (k,(n, 2000))
\end{code}
We have:
\begin{lstlisting}
*Brul> get pSelProj employees
\eval*{get pSelProj employees}
*Brul> put pSelProj employees updatedEmployees0
\eval*{put pSelProj employees updatedEmployees0}
\end{lstlisting}

\subsection{Describing update policies in selection/projection}
\label{sec:policy}

With |pAlign|, we can describe various update policies
for the selection/projection queries. To be concrete,
consider the following selection/projection query:
\begin{align*}
& \mathrlap{\textbf{select}}\phantom{\textbf{where}}\;\mathit{Track}, \mathit{Rating}, \mathit{Album}, \mathit{Quantity}\ \textbf{as}\ v \\
& \mathrlap{\textbf{from}}\phantom{\textbf{where}}\;s \\
& \textbf{where}\; |Quantity > 2|
\end{align*}
which extracts the track, rating, album and quality information from
those music tracks in the source |s| whose quantity is greater than |2|.
Let us see how to write a single BiGUL program so that its |get|
does the above query and its |put| describes a specific update policy.

The first \textsc{BiGUL} program is |u0| below.
\begin{code}
u0    ::  RType -> BiGUL [Record] [Record]
u0 d  =   pAlign
            (\r -> (r !! 4) > RInt 2)
            (\s -> (s !! 0, s!!3))
            (\v -> (v !! 0, v !! 2))
            $(update  (P( (t: _: r: a: q: [])))
                      (P( (t: r: a: q: []) ))
                      (D( t = Replace; r = Replace; a = Replace; q = Replace )))
            (\(t: r: a: q: []) -> (t: d: r: a: q: []))
            (const Nothing)
\end{code}
It tries to match the source records whose |Quantity| is greater than |2|
with the view records by the key (|Track|, |Album|).
There are three cases:
\begin{itemize}

\item A source record is matched with a view record: we first use a
rearrangement function to rearrange the view from a
four-element list |[t,r,a,q]| to a five-element list |[t,_,r,a,q]|
with the second element matched against a widecard.  This rearrangement
function reshapes the view to match the shape of the source.  Then,
the element in the source is |Replace|d by the corresponding element
in the view.

\item A view record that has no matching source record: a new source
record is created with a default value $d$ filled into the
Date.

\item A source record that has no matching view record: we simply
delete this record by returning |Nothing|.

\end{itemize}

Now if we wish to hide the source record by setting its |Quantity| to |0|
rather than deleting it if it has no matching view record,
we could simply change the last line of |u0| and get |u1| as follows.

\begin{code}
u1    ::  RType -> BiGUL [Record] [Record]
u1 d  =   pAlign
            (\r -> (r !! 4) > RInt 2)
            (\s -> (s !! 0, s !! 3))
            (\v -> (v !! 0, v !! 2))
            $(update  (P( (t: _: r: a: q: [])))
                      (P( (t: r: a: q: []) ))
                      (D( t = Replace; r = Replace; a = Replace; q = Replace )))
            (\(t: r: a: q: []) -> (t: d: r: a: q: []))
            (\(t: d: r: a: _: []) -> Just (t: d: r: a: RInt 0:[]))
\end{code}

To test, let us see some concrete running examples of using |u0|.
Recall |s| defined in Section \ref{sec:table}. We can confirm that |get| performs
the query given at the start of this subsection.
{\small
\begin{lstlisting}
*Brul> get (u0 (RInt 2000)) s
\eval*{get (u0 (RInt 2000)) s}
\end{lstlisting}
}
Now suppose that we change the above result (view) to the following
by raising the rating of |Lullaby| from |3| to |4|, raising the quality of |lovesong| from |4| to |7|, and deleting |Trust|:
\begin{code}
v =  [ [RString "Lullaby" , RInt 4, RString "Show"  , RInt 3]
     , [RString "Lovesong", RInt 5, RString "Paris" , RInt 7]
     ]
\end{code}
We can reflect these changes to the source by performing |put| with |u0|.
{\small
\begin{lstlisting}
*Brul> put (u0 (RInt 2000)) s v
\eval*{put (u0 (RInt 2000)) s v}
\end{lstlisting}
}
In the updated source, the changes of rating and quality are correctly reflected, and the music track |Trust| is removed. Note that we may reflect the changes to the source by performing |put| with |u1|, another update strategy, and we will keep the music track |Trust| while setting its quality to be |0|.
{\small
\begin{lstlisting}
*Brul> put (u1 (RInt 2000)) s v
\eval*{put (u1 (RInt 2000)) s v}
\end{lstlisting}
}
