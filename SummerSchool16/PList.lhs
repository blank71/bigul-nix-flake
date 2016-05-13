%include lhs2TeX-macros.lhs

\section{Bidirectional Programming on Lists}

\ignore{

\begin{code}
{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts, DeriveGeneric, ViewPatterns, ScopedTypeVariables, TemplateHaskell #-}

module PList where
import Generics.BiGUL.Error
import Generics.BiGUL.AST
import Generics.BiGUL.Interpreter
import Generics.BiGUL.TH
import Data.List
import Data.Maybe
import Control.Monad.Except
import GHC.Generics
import PBasic
\end{code}

}

In this section, we show many list functions can be bidirectionalized
using BiGUL. To show the correspondence with the original we prefix
the original forward function names with "lens". Note that the forward
function can be automatically derived from the new putback transformation
by calling |get|.

\subsection{lensFoldr}

|foldr| is a simple but useful higher order function on lists.
< foldr f e []      = e
< foldr f e (x:xs)  = f x (foldr f e xs)

Many intereting functions can be defined in |foldr|
< sum = foldr (+) 0
< map f = foldr (\a r -> f a : r) []
< filter p = foldr (\a r -> if p a then a : r else r) []
< reverse p = foldr (\a r -> r ++ [a]) []
< sort = foldr insert []

First, we develop a putback transformation for |foldr|.
\begin{code}
lensFoldr :: BiGUL (a, b) b -> (b->Bool) -> BiGUL ([a], b) b
lensFoldr bx pv =
  Case  [  $(adaptive [| \(x,y) v -> pv v && length x /= 0 |]) $
             \(x,y) v -> ([],y)
        ,  $(normalS [| \(s, e) -> length s == 0 |] ) $
             $(rearrV [| \v -> ((),v) |]) $
               $(update [p| ((),v ) |] [p| (_, v) |] [d| v = Replace |])
        ,  $(normalSV [p| _ |] [p| _ |] ) $
             $(rearrS [| \((x:xs), e) -> (x, (xs,e))  |])
               (Replace `Prod` lensFoldr bx pv) `Compose` bx
        ]
\end{code}
|lengFoldr bx pv| is to synchronize source |(xs,v)| with view |v'|.
If |v'| satisfies |pv|, it will stop. Otherwise,
it will recursively apply |bx| rightwards over the elements of |xs|.
\ignore{
lensFilter :: (a->Bool) -> BiGUL [a] [a]
lensInsert :: Ord a => BiGUL (a,[a]{-sorted-}) [a]{-sorted-}
lensSort :: Ord a => BiGUL [a] [a]
}
\begin{code}
lensReverse :: BiGUL [a] [a]
lensReverse =  $(rearrS [| \s -> (s,[]) |]) $
                  lensFoldr lensSnoc null

lensSnoc :: BiGUL (a,[a]) [a]
lensSnoc = Case  [  $(normal [| \s v -> length v == 1 |]) $
                       $(rearrV [| \[v] -> (v,[]) |]) Replace,
                    $(normal [| \(_,s) v -> length s > 0 |]) $
                       $(rearrS [| \(x,y:ys) -> (y,(x,ys)) |]) $
                          $(rearrV [| \(v:vs) -> (v,vs) |]) $
                             Replace `Prod` lensSnoc,
                    $(adaptive [| \(_,s) v -> null s |]) $
                       \(x,s) _ -> (x, [undefined])
                 ]
\end{code}
\begin{verbatim}
*PList> put lensSnoc (1,[2,3,4]) [10,11,12,13]
Right (13,[10,11,12])
*PList> put lensSnoc (1,[2,3,4]) [10,11,12,13,14]
Right (14,[10,11,12,13])
*PList> put lensSnoc (1,[2,3,4]) [10,11]
Right (11,[10])
*PList> get lensSnoc (100,[1..10])
Right [1,2,3,4,5,6,7,8,9,10,100]

*PList> put lensReverse [1..10] [100..105]
Right [105,104,103,102,101,100]
*PList> put lensReverse [1..10] [100..115]
Left either value mismatch
*PList> get lensReserve [1..10]
*PList> get lensReverse [1..10]
Right [10,9,8,7,6,5,4,3,2,1]
\end{verbatim}

\subsection{Efficiency Issue: |lensFoldr|}

A close look at the definition of |lensFoldr| indicates that it contains many
redundent computations because of the use of |compose|. To see this clear,

\subsection{LensScanr}

\subsection{LensMap}

\begin{code}
lensMap :: BiGUL a b -> BiGUL ([a],[b]) [b]
lensMap bx =  lensFoldr bx' (\v -> length v == 0)
   where  bx' =  $(rearrV [| \(v:vs) -> (v,vs) |]) $
                    bx `Prod` Replace
\end{code}

For testing, we define
\begin{code}
dec1 :: BiGUL Int Int
dec1 = emb g p
  where  g s = s+1
         p s v = v-1
\end{code}
\begin{verbatim}
*PList> put (lensMap dec1) ([0..10],[]) [100..110]
Right ([99,100,101,102,103,104,105,106,107,108,109],[])
*PList> get (lensMap dec1) ([1..10],[])
Right [2,3,4,5,6,7,8,9,10,11]
*PList> put (lensMap dec1) ([0..10],[]) [100]
Right ([99],[])
*PList> put (lensMap dec1) ([0..10],[]) [100..111]
Right ([99,100,101,102,103,104,105,106,107,108,109],[111])
\end{verbatim}
