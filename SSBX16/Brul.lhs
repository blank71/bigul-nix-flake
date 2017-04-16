% !TEX root = tutorial/tutorial.tex

%include lhs2TeX-macros.lhs

\section{Bidirectionalizing relational queries with BiGUL}
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

In this tutorial, we will focus on |align|. As will be seen in Section
\ref{sec:policy}, it can describe more flexible update strategies
(related to selection/projection queries) than relational lenses. 

\subsection{Relational database representation}
\label{sec:table}

A relational table (|RT|) is denoted by a list of records (where the order
does not really matter),
and each record (|Record|) is denoted by a list of attributes of type |RType|, which could
be an integer, a string, a floating point number, or a double-precision floating point number.
\begin{code}
type RT = [Record]
type Record = [RType]
data RType  =  RInt Int 
            |  RString String
            |  RFloat Float
            |  RDouble Double
      deriving (Show, Eq, Ord)
\end{code}
To allow pattern matching on |RType| in BiGUL, we need to declare as follows.
\begin{code}
deriveBiGULGeneric  ''RType
\end{code}

\ignore{

\begin{code}
showRType :: RType -> String
showRType (RInt i) = show i
showRType (RString str) = str
showRType (RFloat f) = show f
showRType (RDouble d) = show d

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

-- revise: many attributes may depend on the same attribute.
-- type FDMap = Map.Map Int [Int]

-- Mapping between source and view attribute, as brul does not support arithmetic operation yet, the correspondence is simply mapping.
type SVMap = Map.Map Int Int

-- update a specific location of a record with a value v with type RType.
uRecord :: Int -> RType -> Record -> Record
uRecord 0 v (x:xs) = v:xs
uRecord i v (x:xs) = x : uRecord (i-1) v xs  


-- find records in the view according to the specific source record attribute value. 
findWith :: Record -> Int -> [Record] -> Int -> Maybe Record
findWith rs is vs iv = 
    case find p vs of
      Just r  -> Just r
      Nothing -> Nothing
  where p :: Record -> Bool
        p vr = vr !! iv == rs !! is

-- for showing error message.
berror s  = error $ "updated record according to functional dependency shall not satisfy p, related source record: " ++ show s
berrorn s = error $ "updated record according to functional dependency shall satisfy p, related source record: " ++ show s

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

\ignore{
A table may have functional dependencies.  We use
|FDMap| to store functional
dependencies of a table
\begin{code}
type FDMap = Map.Map Int [Int]
\end{code}
It maps from one attribute to a list of attributes that depend on it.
Here each attribute is represented by the index in the record list.

Return to the above example. There are functional dependencies
from Track to Date (denoted as $\mathit{Track} \rightarrow
\mathit{Date}$), Track to Rating (denoted as $\mathit{Track}
\rightarrow \mathit{Rating}$), and Album to Quantity (denoted as
$\mathit{Album} \rightarrow \mathit{Quantity}$). This dependencies
can be specified by
\begin{code}
sfdMap :: FDMap
sfdMap = Map.fromList [(0,[1,2]), (3,[4])]
\end{code}
}

\subsection{Relation Alignment}

The alignment of two relational tables, which is related by a selection/projection query, is similar to the key-based list alignment
in Section \ref{sec:alignment}. The difference is that we need to consider
filtering on (i.e., selection of) the source records.
%and maintaining of functional dependency
%on the source elements when updates on the view happen.

\ignore{
Our relation alignment has the form of
<relAlign p ks kv b c h fd
where |p| is a predicate for filtering out those source elements that do not satisfy |p|,
|ks| and |kv| are two functions to extract keys from the source and the view respectively, 
|b| is a \textsc{BiGUL} program to do updating when the source and the view are matched by their keys,
|c| is a function for creating a source element,
|h| is a function to conceal elements in the source,
and |fd| is a function for updating source records according to the functional dependency.
%
Concretely, |relAlign| uses |p| to extract the satisfied
source records, and then uses |ks| and |kv| to match these source
elements with the view elements.  The matching result has three cases,
and each case uses different update operation: when source and view
elements are matched, |b| is used to update the source
element by the view element; when a view element has no corresponding
matching source element, |c| is used to create a source
element from this view element; when a source element has no
corresponding matching view element, |h|
is used to conceal the element (from the view) by either
deleting this source element or modifying it so that it does not
satisfy the filter condition.
}

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
pAlign  ::  forall s v k . (Show s, Show v, Eq k)
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
eval*{get pSelProj employees}
*Brul> put pSelProj employees updatedEmployees0
eval*{put pSelProj employees updatedEmployees0}
\end{lstlisting}
\todo{Josh: The \verb"eval*" commands in this file are temporarily disabled since the file does not typecheck.}

\ignore{
Second, we extend |pAlign| to deal with functional dependency consistency
when updates happen.
To this end, we add a new parameter |fd|, a function for updating source records
to conform functional dependency.
Surprisingly, this is simple. It is suffice to 
extend the fourth case of |pAlign| to apply |fd| when inconsistency happens.

\begin{code}
relAlign :: forall s v k. (Show s, Show v, Eq k, Eq s)
         => (s -> Bool) -> (s -> k) -> (v -> k)
            -> BiGUL s v -> (v -> s) -> (s -> Maybe s)
            -> (s -> s) {- dependency maintaining function -}
            -> BiGUL [s] [v]
relAlign p ks kv b c h fd = Case
  [ $(normalSV (P( [] )) (P( [] )) (P( [] )))
    ==> $(update (P( [] )) (P( [] )) (D( )))
  , $(normal (Q( \(s:ss) (v:vs) -> p s && ks s == kv v )) (Q( \(s:ss) -> p s )))
    ==> $(update (P( x:xs )) (P( x:xs )) (D( x = b; xs = relAlign p ks kv b c h fd )))

  , $(adaptive (Q( \(s:ss) v -> p s && null v)))
    ==> \(s:ss) v -> maybe [] ((:[]) . filterCheck p . fd) (h s) ++ ss
  , $(normal (Q( \(s:ss) v -> not (p s) )) (Q( \(s:ss) -> not (p s) )))
    ==> Case
     [ $(adaptive (Q( \(s:_) _ -> fd s /= s )))
        ==> \(s:ss) _ -> filterCheck (not.p) (fd s) : ss
     , $(normal (Q(\_ _ -> True )) (Q( const True )))
        ==> $(update (P( _:xs )) (P( xs )) (D( xs = relAlign p ks kv b c h fd )))
     ]
  , $(adaptive (Q( \ss (v:vs) -> kv v `elem` map ks (filter p ss) )))
    ==> \ss (v:_) -> uncurry (:) (extract (kv v) ss)
  , $(adaptiveSV (P( _ )) (P( _:_ )))
    ==> \ss (v:_) -> filterCheck p (c v) : ss
  ]
  where
    extract :: k -> [s] -> (s, [s])
    extract k (x:xs)  | p x && ks x == k = (x, xs)
                      | otherwise =  let (y, ys) = extract k xs
                                     in  (y, x:ys)
    filterCheck p v  | p v = v
                     | otherwise = error "error in filter checking"

\end{code}
}

\subsection{Describing update policies in selection/projection}
\label{sec:policy}

With |pAlign|, we can describe various update policies
for the selection/projection queries. To be concrete,
consider the following selection/projection query:
< select Track, Rating, Album, Quantity as v
< from s
< where Quantity > 2
which extracts the track, rating, album and quality information from
those music tracks in the source |s| whose quantity is greater than |2|.
Let us see how to write a single BiGUL program so that its |get|
does the above query and its |put| describes a specific update policy.

The first \textsc{BiGUL} program is |u0| below.
\begin{code}
u0 :: RType -> (Record -> Record) -> BiGUL [Record] [Record]
u0 =  pAlign
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
u1 :: RType -> (Record -> Record) -> BiGUL [Record] [Record]
u1 =  relAlign
        (\r -> (r !! 4) > RInt 2)
        (\s -> (s !! 0, s!!3))
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
*Brul> get u0 s
eval*{get u0 s}
\end{lstlisting}
}
Now suppose that we change the above result (view) to the following
by raising the rating of |Lullaby| from |3| to |4|, raising the quality of |lovesong| from |4| to |7|, and deleting |Trust|:
\begin{code}
v =  [ [RString "Lullaby" , RInt 4, RString "Show"  , RInt 3]
     , [RString "Lovesong", RInt 5, RString "Paris" , RInt 7]
     ]
\end{code}
We can reflect these changes to the source by performing |put|.
{\small
\begin{lstlisting}
*Brul> put u0 s v
eval*{put u0 s v}
\end{lstlisting}
}
In the updated source, the changes of rating and quality are correctly reflected,
and the music track |Trust| is removed.


%Note that the above |(fdFun sfdMap vfdMap svMap v)| denotes a function
%generated by applying |fdFun| to several dependency mappings and view |v|.
%We omit the definition of |fdFun| here.

\ignore{
\begin{code}
d = RInt (-1)

type Source = [Record]
type View = [Record]

brul0 :: BiGUL Source View
brul0 = emb (\s -> fromJust $ get (u0 d id) s)
                  (\s v -> fromJust $ put (u0 d (fdFun sfdMap vfdMap svMap v)) s v)

tb0 = showTable $ fromJust $ put brul0 s v
tf0 = showTable $ fromJust $ get brul0 s

--------------------------------------------------------------------

brul1 :: BiGUL Source View
brul1 = emb (\s -> fromJust $ get (u1 d id) s)
           (\s v -> fromJust $ put (u1 d (fdFun sfdMap vfdMap svMap v)) s v)

tb1 = showTable $ fromJust $ put brul1 s v
tf1 = showTable $ fromJust $ get brul1 s

-- Define the functional dependency on view
vfdMap :: FDMap
vfdMap = Map.fromList [(0, [1]), (2, [3])]

-- Define the mapping relation between source and view.
svMap :: SVMap
svMap = Map.fromList [(0,0), (2,1), (3,2), (4,3)]

-- computation of functional dependency

-- S, and V
fdFun :: FDMap -> FDMap -> SVMap -> View -> Record -> Record
fdFun sfdMap vfdMap svMap vs s = 
  let sfdList = Map.toAscList sfdMap
  in  fdHelper sfdList vfdMap svMap vs s

fdHelper :: [(Int, [Int])] -> FDMap -> SVMap -> View -> Record -> Record
fdHelper []                      vfdMap svMap vs s = s
fdHelper ((from, [to]): ms)      vfdMap svMap vs s = 
  case Map.lookup to svMap of
    Nothing  -> fdHelper ms vfdMap svMap vs s
    Just vto -> 
      case findVFrom vto vfdMap of
        Nothing    -> fdHelper ms vfdMap svMap vs s
        Just vfrom -> 
          case findWith s from vs vfrom of
            Nothing -> fdHelper ms vfdMap svMap vs s
            Just rv -> let s1 = uRecord to (rv !! vto) s
                       in fdHelper ms vfdMap svMap vs s1
fdHelper ((from, (to: tos)): ms)      vfdMap svMap vs s = 
  let s1 = fdHelper [(from, [to])] vfdMap svMap vs s
  in fdHelper ((from, tos): ms) vfdMap svMap vs s


findVFrom :: Int -> FDMap -> Maybe Int
findVFrom vto vfdMap = 
  let vfdList = Map.toAscList vfdMap
  in findVFromHelper vto vfdList

findVFromHelper :: Int -> [(Int, [Int])] -> Maybe Int
findVFromHelper vto [] = Nothing
findVFromHelper vto ((vfrom, vtos) : vs) = 
  case find (\v -> v == vto) vtos of
    Nothing -> findVFromHelper vto vs
    Just _  -> Just vfrom

\end{code}
}
