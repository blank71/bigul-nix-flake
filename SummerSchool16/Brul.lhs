%include lhs2TeX-macros.lhs

\section{Bidirectionalizing relational queries with BiGUL}

\ignore{

\begin{code}
{-# LANGUAGE FlexibleContexts, TemplateHaskell, TypeFamilies #-}

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


\end{code}

}

In work on relational databases, the view-update problem is about how
to translate update operations on the view table to corresponding
update operations on the source table properly. Relational
lenses \cite{Bohannon:2006:RLL:1142351.1142399} try to solve this
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
In this tutorial, we will focus on |align|, which can describe flexible update strategies
related to selection/projection queries. 

\subsection{Relational database representation}

A relational table is a list of records,
and each record is a list of attribute elements of type.
\begin{code}
type RT = [Record]
type Record = [RType]
data RType = RInt Int 
           | RString String
           | RFloat Float
           | RDouble Double
      deriving (Show, Eq, Ord)
\end{code}
Here we introduce a new datatype |RType|. To do pattern matching on
the data of this type, we need to declare
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

-- Mapping between source and view attribute, as brul does not support arithmetic operaiton yet, the correspondence is simply mapping.
type SVMap = Map.Map Int Int

-- update a specific location of a record with a value v with type RType.
uRecord :: Int -> RType -> Record -> Record
uRecord 0 v (x:xs) = v:xs
uRecord i v (x:xs) = x : uRecord (i-1) v xs  


-- find records in the view accordign to the specific source record attribute value. 
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

As an example, consider the table in Figure~\ref{example:s} that
stores five music track records, and each record contains its Track
name, release Date, Rating, Album, and the Quantity of this Album.
It can be represented as follows.
\begin{code}
s  =  [ [RString "Lullaby",  RInt 1989, RInt 3, RString "Galore", RInt 1]
      , [RString "Lullaby",  RInt 1989, RInt 3, RString "Show"  , RInt 3]
      , [RString "Lovesong", RInt 1989, RInt 5, RString "Galore", RInt 1]
      , [RString "Lovesong", RInt 1989, RInt 5, RString "Disintegration" , RInt 4]
      , [RString "Trust",    RInt 1992, RInt 4, RString "Wish"  , RInt 5]
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

\subsection{Align}

\begin{code}
align :: (Eq a, Show a, Eq b, Show b)
      => (a -> Bool)
      -> (a -> b -> Bool)
      -> BiGUL a b
      -> (b -> a)
      -> (a -> Maybe a)
      -> (a -> a)  -- update functional dependency
      -> BiGUL [a] [b]
align p match b create conceal fd =  
  Case [ $(adaptiveSV [| \ss -> null (filter p ss) && map fd ss /= ss |] [p| [] |]) 
         ==> \ss _ -> map (\s1 -> let s2 = fd s1 in if p s2 then berror s1 else s2) ss    
       , $(adaptiveSV [| not . null . filter p |] [p| [] |])
         ==> \ss _ -> catMaybes (map (\s -> 
          let s1 = if p s then conceal s else Just s 
          in (maybe Nothing 
                (\s1 -> let s2 = fd s1 in if p s2 then berror s1 else (Just s2)) -- after fd, check p
                s1
             )) ss) -- using fd to update
       , $(adaptiveSV [| \ss -> not (null (filter p ss)) && not (p (head ss)) && (fd (head ss) /= head ss) |] [p| _:_ |])
         ==> \(s:xs) _ -> let s1 = fd s in if p s1 then berror s else s1: xs -- after fd, check p    
       , $(normalSV [| \ss -> null (filter p ss) |] [p| [] |] [| const True |])  
         ==> $(update [p| _ |] [p| [] |] [d| |])
       , $(normalSV [| \ss -> not (null (filter p ss)) && not (p (head ss)) |] [p| _:_ |] [| const True |])
         ==> $(update [p| _:vs |] [p| vs |] [d| vs = align p match b create conceal fd |])
       , $(normal [| \ss vs -> not (null (filter p ss)) && p (head ss) && not (null vs) && match (head ss) (head vs) |]
                  [| \ss -> not (null (filter p ss)) && p (head ss) |]) 
         ==> $(update [p| v: vs |] [p| v : vs |]
                      [d| v  = b
                          vs = align p match b create conceal fd |])
       , $(adaptiveSV [| const True |] [p| _:_ |])
         ==> \ss (v:_) -> case find (flip match v) (filter p ss) of
                          Nothing -> let s1 = fd (create v)
                                     in if p s1 
                                          then s1 :ss
                                          else berrorn s1
                          Just s  -> s :delete s ss ]

\end{code}

\subsection{Describing update policies in selection/projection}

\begin{code}
--------------------------------------------------------------
-- The first update program
-- Delete the unmatched source record
u0 :: RType -> (Record -> Record) -> BiGUL [Record] [Record]
u0 d =
  align
    (\r -> (r !! 4) > RInt 2)
    (\s v -> (s !! 0 == v !! 0) && (s !! 3 == v !! 2))
    $(update [p| (t: _: r: a: q: [])|]
             [p| (t: r: a: q: []) |]
             [d| t = Replace; r = Replace; a = Replace; q = Replace |])
    (\(t: r: a: q: []) -> (t: d: r: a: q: []))
    (\rs -> Nothing)

--------------------------------------------------------------
-- The second update program
-- Update the unmatched source record
u1 :: RType -> (Record -> Record) -> BiGUL [Record] [Record]
u1 d =
  align
    (\r -> (r !! 4) > RInt 2)
    (\s v -> (s !! 0 == v !! 0) && (s !! 3 == v !! 2))
    $(update [p| (t: _: r: a: q: [])|]
             [p| (t: r: a: q: []) |]
             [d| t = Replace; r = Replace; a = Replace; q = Replace |])
    (\(t: r: a: q: []) -> (t: d: r: a: q: []))
    (\(t: d: r: a: _: []) -> Just (t: d: r: a: RInt 1:[]))
\end{code}
