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
\end{code}

}

\subsection{Foldr}

\begin{code}
lensFoldr :: (BiGUL (a, b) b) -> (BiGUL ([a], b) b)
lensFoldr bx =
  Case  [ $(normalS [| \(s, e) -> length s == 0 |] ) $
            $(rearrV [| \v -> ((),v) |]) $
              $(update [p| ((),v ) |] [p| (_, v) |] [d| v = Replace |])
        , $(normalSV [p| _ |] [p| _ |] ) $
            $(rearrS [| \((x:xs), e) -> (x, (xs,e))  |])
              (Replace `Prod` lensFoldr bx)
              `Compose`
              bx
        ]
\end{code}

\begin{code}
lensMap :: BiGUL a b -> BiGUL [a] [b]
lensMap bx = $(rearrS [| \s -> (s, []) |])
  (lensFoldr ($(rearrV [| \(v:vs) -> (v,vs) |]) $ bx `Prod` Replace))
\end{code}
