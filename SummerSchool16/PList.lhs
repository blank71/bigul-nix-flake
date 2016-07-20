%include lhs2TeX-macros.lhs

\section{Bidirectional Programming on Lists}

\ignore{

\begin{code}
{-# LANGUAGE FlexibleContexts, TemplateHaskell, TypeFamilies #-}

module PList where
import Generics.BiGUL
import Generics.BiGUL.Interpreter
import Generics.BiGUL.TH
import Generics.BiGUL.Lib
import Data.List
import Data.Maybe
import Control.Monad.Except
import GHC.Generics
import PBasic
\end{code}

}

In this section, we show many list functions can be bidirectionalized
using BiGUL. To show the correspondence with the original list functions,
we prefix
the original forward function names with "lens". Note that the forward
function can be automatically derived from the new putback transformation
by calling |get|.

We shall focus on |foldr|, which is a simple but useful higher order function on lists:
< foldr f e []      = e
< foldr f e (x:xs)  = f x (foldr f e xs)
where many interesting functions can be defined in |foldr|
< sum = foldr (+) 0
< map f = foldr (\a r -> f a : r) []
< filter p = foldr (\a r -> if p a then a : r else r) []
< reverse p = foldr (\a r -> r ++ [a]) []
< sort = foldr insert []

First, we develop a putback version for |foldr|.
\begin{code}
lensFoldr :: (Show a, Show b) => BiGUL (a, b) b -> (b->Bool) -> BiGUL ([a], b) b
lensFoldr bx pv =
  Case  [  $(adaptive [| \(x,y) v -> pv v && length x /= 0 |]) 
             ==> \(x,y) v -> ([],y)
        ,  $(normal [| \(s,_) v -> null s |] [| \(s,_) -> null s |]) 
             ==> $(rearrV [| \v -> ((),v) |]) $
                    $(update [p| (_, v) |] [p| ((),v ) |] [d| v = Replace |])
        ,  $(normalSV [p| _ |] [p| _ |] [| \(s,_) -> not (null s) |])
             ==> $(rearrS [| \((x:xs), e) -> (x, (xs,e))  |])
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

Next, we show that many list functions can be bidirectionalized using
|lensFoldr|. As the first example, we consider bidirectionalize |map|.
It can be easily defined in terms of |lensFoldr|.

\begin{code}
lensMap :: (Show a, Show b) => BiGUL a b -> BiGUL ([a],[b]) [b]
lensMap bx =  lensFoldr bx' null
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
Just ([99,100,101,102,103,104,105,106,107,108,109],[])
*PList> get (lensMap dec1) ([1..10],[])
Just [2,3,4,5,6,7,8,9,10,11]
\end{verbatim}
Now we give another example of |reverse|.
\begin{code}
lensReverse :: Show a => BiGUL [a] [a]
lensReverse =  Case  [
                        $(adaptive [| \s v -> length s < length v |])
                          ==> \s v -> v
                     ,  $(normalSV [p| _ |] [p| _ |] [| \ s -> True |])
                          ==> $(rearrS [| \s -> (s,[]) |]) $
                                lensFoldr (lensSwap `Compose` lensSnoc) null
                     ]

lensSnoc :: Show a => BiGUL ([a],a) [a]
lensSnoc = Case  [  $(normal [| \s v -> length v == 1 |] [| \(s,_) -> null s |])
                       ==> $(rearrV [| \[v] -> ([],v) |]) Replace
                 ,  $(normal [| \(s,_) v -> length s > 0 |] [| \(s,_) -> length s > 0 |])
                       ==> $(rearrS [| \(y:ys,x) -> (y,(ys,x)) |]) $
                              $(rearrV [| \(v:vs) -> (v,vs) |]) $
                                  Replace `Prod` lensSnoc
                 ,  $(adaptive [| \(s,_) v -> null s |]) 
                       ==> \(s,x) _ -> ([undefined], x)
                 ]

lensSwap :: (Show a, Show b) => BiGUL (a,b) (b,a)
lensSwap = $(rearrS [| \(x,y) -> (y,x) |]) Replace
\end{code}
Below are some testing examples.
\begin{verbatim}
*PList> put lensSnoc ([2,3,4],1) [10,11,12,13]
Just ([10,11,12],13)
*PList> put lensSnoc ([2,3,4],1) [10,11,12,13,14]
Just ([10,11,12,13],14)
*PList> put lensSnoc ([2,3,4],1) [10,11]
Just ([10],11)
*PList> get lensSnoc ([1..10], 100)
Just [1,2,3,4,5,6,7,8,9,10,100]

*PList> put lensReverse [1..10] [100..105]
Just [105,104,103,102,101,100]
*PList> put lensReverse [1..10] [100..115]
Just [115,114,113,112,111,110,109,108,107,106,105,104,103,102,101,100]
*PList> get lensReverse [1..10]
Just [10,9,8,7,6,5,4,3,2,1]
\end{verbatim}

\ignore{
\subsection{Efficiency Issue: |lensFoldr|}

A close look at the definition of |lensFoldr| reveals that it contains many
redundant computations because of the use of |Compose| that calls |get| as many
times as the number of calls of |Compose|. Put it more concretely,
< put (lensFoldr bx (const True)) ([x1,x2,...,xn],e) v
would call
< get (lensFoldr bx (const True)) ([x2,...,xn],e),
< ...,
< get (lensFoldr bx (const True)) ([],e).


\subsection{LensScanr}

\subsection{LensMap}
}
