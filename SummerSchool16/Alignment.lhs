% !TEX root = paper.tex

%include lhs2TeX-macros.lhs

\section{Positional, key-based, and delta-based list alignment}

\ignore{
\begin{code}
{-# LANGUAGE TemplateHaskell, TypeFamilies, ScopedTypeVariables #-}

import Generics.BiGUL
import Generics.BiGUL.TH
import Generics.BiGUL.Lib
import Generics.BiGUL.Interpreter

import Data.Tuple
import Data.Maybe
import Data.List
\end{code}
}

List alignment is one of the tasks that frequently show up when developing bidirectional applications.
When the source and view are both lists, and the |get| direction (i.e., the consistency relation) is a |map|, how do we put an updated view --- the updates on which might involve insertions, deletions, in-place modifications, and reordering --- into the source?

Throughout the section, we use a concrete example to introduce three variations of the list alignment problem.
Suppose that we represent a payroll database as a list.
(This is a slightly inadequate setting for explaining list alignment, because entries in a database are usually unordered. But let us assume that order matters.)
Each entry is a triple consisting of an identification number (``id'' henceforth), a name, and a salary number:
\begin{code}
type Source = (Id, (Name, Salary))

type Id      =  Int
type Name    =  String
type Salary  =  Int
\end{code}
For example, here is a sample payroll database:
\begin{code}
employees  ::  [Source]
employees  =   [  (0  , ("Zhenjiang"  , 1000  ))
               ,  (1  , ("Josh"       , 400   ))
               ,  (2  , ("Jeremy"     , 2000  ))]
\end{code}
Suppose that the human resource department, which is in charge of hiring or sacking employees, has no say on salary numbers, so the entries of the database are presented to them only as pairs of ids and names:
\begin{code}
type View = (Id, Name)
\end{code}
For example, |employees| is presented to them as
\begin{spec}
[(0, "Zhenjiang"), (1, "Josh"), (2, "Jeremy")]
\end{spec}
on which they can make modifications.
It is easy to write a BiGUL program to synchronize the source and view elements:
\begin{code}
bx :: BiGUL Source View
bx = Replace `Prod` $(rearrS [| \(n, _) -> n |]) Replace
\end{code}
The problem is then how to determine the correspondences between sources and views in the two lists, so |bx| can be applied to the right pairs.

\subsection{Positional alignment}

As a first exercise, we consider the simplest strategy, which matches source and view elements by their positions in the lists.
If the source list has more elements than the view list, the extra elements at the tail are simply dropped; if the former has less elements, then new source elements have to be created, which we can specify as a function:
\begin{code}
cr :: View -> Source
cr (i, n) = (i, (n, 0))
\end{code}
The salary is set to zero, which can be taken care of by the accounting department later, for example.
In general, we can abstract the source and view types and |bx| and |cr| as parameters, so the alignment program we write can be widely applicable.
Here is how we implement positional alignment, which is fairly standard:
\begin{code}
posAlign :: (Show s, Show v) => BiGUL s v -> (v -> s) -> BiGUL [s] [v]
posAlign b c = Case
  [ $(normalSV [p| [] |] [p| [] |] [p| [] |])
    ==> $(update [p| [] |] [p| [] |] [d| |])
  , $(normalSV [p| _ : _ |] [p| _ : _ |] [p| _ : _ |])
    ==> $(update [p| x:xs |] [p| x:xs |] [d| x = b; xs = posAlign b c |])
  , $(adaptiveSV [p| _ : _ |] [p| [] |])
    ==> \ _ _ -> []
  , $(adaptiveSV [p| [] |] [p| _ : _ |])
    ==> \ _ (v : _) -> [c v]
  ]
\end{code}
The normal branches deal with the situations where both lists are empty or non-empty, and the adaptive branches remove or create elements when the lengths of the two lists differ.

The |get| direction of |posAlign| does exactly what we want it to do:
\begin{verbatim}
*Main> get (posAlign bx cr) employees
Just [(0,"Zhenjiang"),(1,"Josh"),(2,"Jeremy")]
\end{verbatim}
It should be quite obvious, though, that the |put| direction is not so useful for our purpose.
If we sack Josh:
\begin{code}
updatedEmployees0  ::  [View]
updatedEmployees0  =   [(0, "Zhenjiang"), (2, "Jeremy")]
\end{code}
then the database will updated to:
\begin{verbatim}
*Main> put (posAlign bx cr) employees updatedEmployees0
Just [(0,("Zhenjiang",1000)),(2,("Jeremy",400))]
\end{verbatim}
where Jeremy inadvertently gets Josh's original salary.
Even if we do not remove any employee, we may still want to reorder them:
\begin{code}
updatedEmployees1  ::  [View]
updatedEmployees1  =   [(2, "Jeremy"), (0, "Zhenjiang"), (1, "Josh")]
\end{code}
and now everyone gets a wrong salary:
\begin{verbatim}
*Main> put (posAlign bx cr) employees updatedEmployees1
Just [(2,("Jeremy",1000)),(0,("Zhenjiang",400)),(1,("Josh",2000))]
\end{verbatim}
This first exercise shows that the alignment problem is inherently one that should be solved from the |put| direction.
It is easy to implement the |get| direction correctly, but what matters is the |put| behavior.

\subsection{Key-based alignment}

A more reasonable strategy is to match source and view elements by some \emph{key} value.
In our example, we can use the id as the key.
Key-based alignment might seem much more complex than positional alignment, but, in fact, we can just revise |posAlign| to get a BiGUL program for key-based alignment!

First of all, we need to somehow obtain the keys.
In our example, on both the source and view we can use |fst| to extract the key value.
In general, we can further parametrize the alignment program with key extraction functions:
\begin{spec}
keyAlign  ::  forall a b k. (Show a, Show b, Eq k)
          =>  (a -> k) -> (b -> k) -> BiGUL a b -> (b -> a) -> BiGUL [a] [b]
keyAlign ks kv b c = Case undefined
\end{spec}
The first normal branch of |posAlign| still works perfectly.
As for the second normal branch, we should revise the main condition to also require that the head elements of the two lists have the same key value:
\begin{spec}
\(s:ss) (v:vs) -> ks s == kv v
\end{spec}
The first adaptive branch, again, works well.
The second adaptive branch, on the other hand, is no longer applicable:
Since the main condition of the second normal branch has been tightened, it is no longer the case that this adaptive branch will receive only empty source lists.
In fact, whether the source list is empty or not is not relevant here --- what matters now is whether the key of the first view is in the source list.
If it is, then we bring the (first) source element with the same key value to the head position, and the second normal branch can take over; otherwise, we create a new source element.
This gives us key-based alignment:
\begin{code}
keyAlign  ::  forall s v k. (Show s, Show v, Eq k)
          =>  (s -> k) -> (v -> k) -> BiGUL s v -> (v -> s) -> BiGUL [s] [v]
keyAlign ks kv b c = Case
  [ $(normalSV [p| [] |] [p| [] |] [p| [] |])
    ==> $(update [p| [] |] [p| [] |] [d| |])
  , $(normal [| \(s:ss) (v:vs) -> ks s == kv v |] [p| _ : _ |])
    ==> $(update [p| x:xs |]  [p| x:xs |]
                              [d| x = b; xs = keyAlign ks kv b c |])
  , $(adaptiveSV [p| _ : _ |] [p| [] |])
    ==> \ _ _ -> []
  , $(adaptive [| \ss (v:vs) -> kv v `elem` map ks ss |])
    ==> \ss (v : _) -> uncurry (:) (extract (kv v) ss)
  , $(adaptiveSV [p| _ |] [p| _ : _ |])
    ==> \ss (v : _) -> c v : ss
  ]
  where
    extract :: k -> [s] -> (s, [s])
    extract k (x:xs)  | ks x == k  =  (x, xs)
                      | otherwise  =  let  (y, ys) = extract k xs
                                      in   (y, x:ys)
\end{code}

Back to our employment example.
The |get| direction behaves the same:
\begin{verbatim}
*Main> get (keyAlign fst fst bx cr) employees
Just [(0,"Zhenjiang"),(1,"Josh"),(2,"Jeremy")]
\end{verbatim}
Unlike positional alignment, view element deletion can now be reflected correctly:
\begin{verbatim}
*Main> put (keyAlign fst fst bx cr) employees updatedEmployees0
Just [(0,("Zhenjiang",1000)),(2,("Jeremy",2000))]
\end{verbatim}
And reordering as well:
\begin{verbatim}
*Main> put (keyAlign fst fst bx cr) employees updatedEmployees1
Just [(2,("Jeremy",2000)),(0,("Zhenjiang",1000)),(1,("Josh",400))]
\end{verbatim}

So it seems that key-based alignment is just what we need.
Indeed, key-based alignment usually works well, but there is an important assumption:
The key values should not be changed.
If, for example, we decide to assign a different id to Josh:
\begin{code}
updatedEmployees2  ::  [View]
updatedEmployees2  =   [(0, "Zhenjiang"), (100, "Josh"), (1, "Jeremy")]
\end{code}
Then the effect is the same as sacking Josh and then hiring him again, whose salary is thus reset:
\begin{verbatim}
*Main> put (keyAlign fst fst bx cr) employees updatedEmployees2
Just [(0,("Zhenjiang",1000)),(100,("Josh",0)),(1,("Jeremy",400))]
\end{verbatim}
The problem is that we cannot distinguish modification from deletion and insertion pairs.
To be able to have such distinction, we introduce the notion of \emph{deltas}, with which the links between source and view elements can be kept track of.

\subsection{Delta-based alignment}

A delta between a source list and a view list is a list of pairs of associated positions:
\begin{code}
type Delta = [(Int, Int)]
\end{code}
For example, the delta we have in mind between |employees| and |updatedEmployees2| is |[(0,0), (1,1), (2,2)]|, which, in particular, associates the source and view entries for Josh since |(2,2)| is included, instead of |[(0,0), (1,1)]|, which indicates that Josh's source entry is not associated with any view entry and should be deleted, and that Josh's view entry is not associated with any source entry and is thus new.
Deltas can easily represent reordering as well.
For example, we would supply the delta between |employees| and |updatedEmployees1| as |[(0,1), (1,2), (2,0)]|, associating the 0th element in the source --- namely the one for Zhenjiang --- with the 1st element in the view, and so on.

So the input now includes not only source and view lists but also a delta between them.
Recall key-based alignment: What it does overall is to bring the first matching source element to the front for each view element, so the source list is updated throughout execution, with the links between the source and view elements gradually and implicitly restored.
If we are doing something similar with delta-based alignment, then when the source list is updated, the delta should also be updated to reflect the restored consistency.
This suggests that the delta should be paired with the source list, so it can be updated.
The type we use for the delta-based alignment program is thus:
\begin{spec}
deltaAlign  ::  (Show s, Show v)
            =>  BiGUL s v -> (v -> s) -> BiGUL ([s], Delta) [v]
deltaAlign b c = Case undefined
\end{spec}

Here we take a simpler approach to implementing |deltaAlign|, analyzing the problem into just two cases:
The delta can tell us either that the source and view elements are all in correspondence, so a simple positional alignment suffices, or that we need to do some rearrangement of the source elements, which can be done by adaptation.
In BiGUL:
\begin{code}
idDelta     ::  [s] -> Delta
idDelta ss  =   [ (i, i) | i <- [0..length ss] ]

deltaAlign  ::  (Show s, Show v)
            =>  BiGUL s v -> (v -> s) -> BiGUL ([s], Delta) [v]
deltaAlign b c = Case
  [ $(normal [| \(ss, d) vs -> length ss == length vs && d == idDelta ss |] [p| _ |])
    ==> $(rearrS [| \(ss, _) -> ss |])$ posAlign b c
  , $(adaptive [| \_ _ -> otherwise |])
    ==>  \(ss, d) vs ->
           let   d'   = map swap d
                 ss'  = [ maybe (c v) (ss !!) (lookup j d') | (v, j) <- zip vs [0..] ]
           in (  ss', idDelta ss')
  ]
\end{code}
The source and view lists are in full correspondence if and only if they have the same length and the delta associates all their elements positionally.
This full positional delta can be computed by |idDelta|.
When this is the case, it suffices to call |posAlign| to carry out an element-wise synchronization, since no rearrangement is required.
Otherwise, we enter the adaptive branch, which constructs a new source list in full correspondence with the view list, drawing elements from the original source list or create new ones as the delta dictates.
The new source list is in full correspondence with the view list, so the delta we pair with it is the one computed by |idDelta|.

Only when performing |put| does supplying a delta make sense.
When performing |get|, however, we still need to supply a delta since it is part of the source; but there is natural choice, which is |idDelta|.
So we define:
\begin{code}
putDeltaAlign  ::  (Show s, Show v)
               =>  BiGUL s v -> (v -> s) -> [s] -> Delta -> [v] -> Maybe [s]
putDeltaAlign b c ss d vs = fmap fst (put (deltaAlign b c) (ss, d) vs)

getDeltaAlign  ::  (Show s, Show v)
               =>  BiGUL s v -> (v -> s) -> [s] -> Maybe [v]
getDeltaAlign b c ss = get (deltaAlign b c) (ss, idDelta ss)
\end{code}
It is easy to prove that, given the same |b|~and~|c|, these two functions do form a lens.
The key observation is that the delta produced by |put (deltaAlign b c)| is necessarily one computed by |idDelta|, so, for example, in \ref{eq:PutGet}, throwing away the delta in the |put| direction is fine because it can be recomputed by |idDelta|, and the |get| direction can resume from exactly the same source pair.

Back to our example. We can now update the id of Josh without resetting his salary by providing a full delta indicating that there are only in-place updates:
\begin{verbatim}
*Main> putDeltaAlign bx cr employees
         [(0,0), (1,1), (2,2)] updatedEmployees2
Just [(0,("Zhenjiang",1000)),(100,("Josh",400)),(1,("Jeremy",2000))]
\end{verbatim}
Besides obvious things like reordering, we can also do some fairly subtle things now:
If we actually sack Josh and replace him with a new Josh (inheriting the original Josh's id) whose salary should be reset to be re-considered, we can say so by providing a partial delta:
\begin{verbatim}
*Main> putDeltaAlign bx cr employees [(0,0), (2,2)]
         =<< getDeltaAlign bx cr employees
Just [(0,("Zhenjiang",1000)),(1,("Josh",0)),(2,("Jeremy",2000))]
\end{verbatim}

\subsubsection{One alignment to rule them all.}
Where do deltas come from?
In general, we may provide a view editor which monitors how the view is modified and produces a suitable delta.
But in more specialized scenarios, deltas can simply be computed by, for example, comparing the source and view.
We can formalize this delta computation as:
\begin{code}
type DeltaStrategy s v = [s] -> [v] -> Delta
\end{code}
and further parametrize |putDeltaAlign|:
\begin{code}
putDeltaAlignS  ::  (Show s, Show v) => DeltaStrategy s v
                ->  BiGUL s v -> (v -> s) -> [s] -> [v] -> Maybe [s]
putDeltaAlignS dst b c ss vs = putDeltaAlign b c ss (dst ss vs) vs
\end{code}
Positional alignment and key-based alignment can then be seen as special cases of delta-based alignment using specific delta-computing strategies.
For positional alignment, we simply compute the identity delta:
\begin{code}
byPosition :: DeltaStrategy s v
byPosition ss _ = idDelta ss
\end{code}
And for key-based alignment, we compute a delta associating source and view elements with the same key:
\begin{code}
byKey :: Eq k => (s -> k) -> (v -> k) -> DeltaStrategy s v
byKey ks kv ss vs =
  let  sis = zip ss [0..]
  in   catMaybes  [  fmap (\(_, i) -> (i, j)) (find (\(s, _) -> ks s == kv v) sis)
                  |  (v, j) <- zip vs [0..] ]
\end{code}
We can check that these strategies indeed give us positional and key-based alignment:
\begin{verbatim}
*Main> putDeltaAlignS byPosition bx cr employees updatedEmployees0
Just [(0,("Zhenjiang",1000)),(2,("Jeremy",400))]

*Main> putDeltaAlignS (byKey fst fst) bx cr employees updatedEmployees1
Just [(2,("Jeremy",2000)),(0,("Zhenjiang",1000)),(1,("Josh",400))]
\end{verbatim}
