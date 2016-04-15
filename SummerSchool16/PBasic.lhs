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

The core of BiGUL consists of three basic primitives and three
combinators to gluing smaller bidirectional transformations to form
a bigger one.

\subsection{Three Primitives}
 
BiGUL provides three basic primitives:
< Skip     :: BiGUL s ()
< Replace  :: BiGUL s s
< Fail     :: BiGUL s v

\subsection{Two Combinators}

 
\subsection{Utilites}
