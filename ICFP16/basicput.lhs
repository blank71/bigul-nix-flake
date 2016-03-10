%include lhs2tex.lhs
%format `Prod`="\times"
\begin{comment}
\begin{code}
{-# LANGUAGE TemplateHaskell #-}
module BasicPut where

import Generics.BiGUL.AST
import Generics.BiGUL.TH
\end{code}
\end{comment}
\begin{code}
myBX :: BiGUL (Int, (Char, Int)) (Int, Char)
myBX = Replace `Prod` $(rearrV   [| \ c -> (c, ()) |])
                                 (Replace `Prod` Skip)
\end{code}
