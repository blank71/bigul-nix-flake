%include lhs2tex.lhs
\begin{code}
keyMatch  ::  ((K,V1) -> (K,(V1,V2)))
          ->  BiGUL (K,(V1,V2)) (K,V1)
          ->  BiGUL [(K,(V1,V2))] [(K,V1)]
keyMatch c u = TODO
\end{code}
