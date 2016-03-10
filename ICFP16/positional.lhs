%include lhs2tex.lhs
%format V1="V_1"
%format V2="V_2"
\begin{code}
mapL  ::  ((K,V1) -> (K,(V1,V2)))
      ->  BiGUL (K,(V1,V2)) (K,V1)
      ->  BiGUL [(K,(V1,V2))] [(K,V1)]
mapL c u = Case
  [ $(normalSV [p| [] |] [p| [] |])$
      $(rearrV [| \ [] -> () |]) Skip
  , $(adaptiveV [p| [] |])$ \ _ _ -> []
  , $(normalSV [p| (_ : _) |] [p| (_ : _) |])$
      $(rearrV [| \ (v:vs) -> (v, vs) |])$
        $(rearrS [| \(s:ss) -> (s, ss) |])$
          u `Prod` mapL c u
  , $(adaptiveV [p| (_ : _) |])$
    \ _ (v : _) -> [c v]
  ]
\end{code}
