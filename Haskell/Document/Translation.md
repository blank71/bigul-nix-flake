    Source: (a, b)
    View: $v

E1. UPDATE
    BiFlux:
>     Replace $s/a WITH $v
>   == SingleReplace Nothing (CPathSlash (CPathVar "$s") (CPathString "a")) (XQPath (CPathVar "$v"))
    BiGUL:
>    Update (UProd (Rearr RVar (EDir DVar) Replace) (UVar Skip))
    Or:
>     Rearr RVar (EProd (EDir DVar) (EConst ())) (Update (UProd (UVar Replace) (UVar Skip)))
    Memo: UPat is constructed according to both source Path and Source Type.
    For a replace statement in BiFlux:
>     SingleReplace {-(Maybe Pat)-} CPath XQExpr
    The translation would be:
      1. Translate CPath on source a an Update UPat.
>         Update :: UPat m s v ->BiGUL m s v
>         UPat :: (* -> *) -> * -> * -> *
      2. According to XQExpr part to do rearrangement.
>         Rearr :: RPat v env con -> XQExpr env v'-> BiGUL m s v
      3. For each variable point in Source pat, Fill in the Replacement
>        Replace :: BiGUL m s s
    So in step 1, we need translate the XML Path in BiFlux to Pattern matching in BiGUL.
    This would be an interesting work.

-- Put aside the E11
------- ignre ------------
E11. How to handle WHERE condition ?
    BiFlux:
>      Replace $s/a WITH $v WHERE $s/b = 'b'
    BiGUL:
>      Update (UProd (UVar REPLACE) (UConst Skip)) ++ ?
    I think the possible way by using existing operators in BiGUL is the Align.
>   Align (evalToBool($s/b='b')) (align-by-position) (the-same-whith-previous) (..) (..)
   And we need the following operations:
    1. (\_ _ -> True) 
    2. v -> m s: generate a special 'CREATE' function to create a tempalte source with an empty view first.
    3. s -> m (Maybe s)) : Deletion directly.
------- end -------------

E2. UPDATE .. BY ..
    BiFlux:
>      UPDATE $a IN $s/a BY
        ....
>      UpdateSource (Maybe Pat) CPath Stmts
    BiGUL:
>      Update (UProd (UVar (...)) (UVar Skip))  

      Note if having Pat here, the translation would be combined with CPath. as in fact, CPath is translated into Pattern.
      For example,
>        UPDATE [$a as s:a, $b as s:b] IN $s BY REPLACE $a WITH $v

E3. IF condition on source
    BiFlux:
>     IF $s/b = 'b' THEN REPLACE $s/a WITH $v ELSE REPLACE $s/a WITH $v
     AST:
>     StmtIf BoolExpr Stmts Stmts
    BiGUL:
>     CaseS [
>       (evalToBool($s/b = 'b'), UPDATE (UPat (UProd (UVar (Rearr RVar (EDir DVar) Replace)) (UConst Skip)))),
>       ( not(evalToBool($s/b = 'b') === True {- const (return True)-}), UPDATE (UPat (UProd (UVar (Rearr RVar (EDir (DVar)) Replace)) (UConst Skip))))
>       ]
     AST:
>  CaseS :: [(s -> m Bool, CaseSBranch m s v)] -> BiGUL m s v
>  data CaseSBranch  m s v = Normal (BiGUL m s v) | Adaptive (s -> m s)

   TODO:
   What does evalToBool like ?
>  \s1 -> if s1 == 'b' then return True else return False

   Will we handle this ?
> \s1 -> if s1 == XQElem 'b' (XQPath (CPathString "b")) then return True else return False
   The problem is s1 is a subtree of sour s, while there the type shall be s -> m Bool

E31. Expr with arithmetic operations. (TODO)
    BiFlux:
>     IF $s/b = 'b' THEN REPLACE $s/a WITH $v ELSE REPLACE $s/a WITH $v + 1
    BiGUL:
>     ?
    I think this is related to Expr rearrangement.
    Becuause we haven't consider arithmetic operators yet.

E4. IF contition on view :
    BiFlux:
>      IF $v = 'b' THEN REPLACE $s/a WITH $v ELSE REPLACE $s/a WITH $v
    How to handle unsued view variables, for example, suppose view is a tuple ($v1, $v2)
>      $v1 = 'b', $v2
>      EProd (EComapre (EDir DVar) 'b'), (EDir DVar)
    Return to the previous example, the BiGUL:
>      Rearr RVar (ECompare (EDir DVar) 'b') (
>         CaseV [
>             (CaseVBranch (PLeft (PConst ())) (then-branch)), -- you shall not use $v1 anymore later.
>             (CaseVBranch (PRight PVar) (else-branch)) -- else branch pass the variable to the rest.
>           ]
>        )
>  ECompare :: Expr orig v' -> v' -> Expr orig (Either () v')
   BiFlux:
    Suppose v is ($v1, ($v2, $v3)) {- v is deconstructed using pattern matcing, a product is constructed with right-baised parensis. -}
>   IF <c><a>$v1</a><b>$v2</b></c> = <c><a>x</a><b>y</b></c> THEN .. ELSE ...
   BiGUL:
>   Rearr (RProd RVar (RProd RVar RVar)) 
>         (EProd (EComapre (EIn (EProd (EIn (EDir (DLefit DVar))) (EIn (EDir (DRight (DLeft DVar)))))) (......)) (EDir (DRight (DRight DVar)))) 
>         (
>          CaseVBranch (PProd (Left ()) PVar ) (...),
>          CaseVBranch (PProd (PRight (POut (PProd (POut PVar) (POut PVar)))) (PVar)) (...)
>         )

>     CaseV :: [(CaseVBranch m s v)] -> BiGUL m s v
>     data CaseVBranch m s v where 
>       CaseVBranch :: Pat v v' -> BiGUL m s v' -> CaseVBranch m s v

-- skip this LetS --
E5. LetS

    BiFlux:
>      LET $a = <p>{$s/a}</p> IN REPLACE $a WITH $V
>      StmtLet Pat XQExpr Stmts
    BiGUL:
>      Rearr RVar (EIn (EDir ..)) (trans(REPLACE $a WITH $v))
Qestion: Do we need Rearr on source ?
--- end -----

E6. LetV
    BiFlux:
>      Let $vtemp = <a>{$v}</a> IN REPLACE $s/a WITH $vtemp
    BiGUL:
>      Rearr RVar (EIn (EDir DVar)) (...)
   How about this ?
>      Let $vtemp = <a>{$v/a}</a> IN REPLACE $s/a WITH $vtemp
Question:  If we know there is only an 'a' tag under a, can we write this expression ?
>      Rearr (ROut RVar) (EIn (EDir (DVar))) (...)  -- So the RPat shall fetch the real value we want.

E7. CaseS
   BiFlux:
>     case $s of
>        bookmark[..] -> u1
>        folder[..] -> u2
>     StmtCase XQExpr [(Pat, Stmts)]
  BiGUL:
>  Update (UVar
>    CaseS [
>      (evalPatToBool(pat1), t(pat1, u1)),
>      (evalPatToBool(pat2), t(pat2, u2))
>    ]
>  )
>   t(pat, u) = Update (..)
>   Update :: UPat m s v -> BiGUL m s v

---- ignore -----
   how about:
>     case $s/a of 
>        bookmark[$b1] -> u($s|$b1 )
    using: 
>     Update (...)
---- end ---- 

 When translating u($1|$b1), analyse whether using $s or not.

E8. CaseV
   BiFlux:
>     case $v of
>       bookmark[$title AS string] -> u1
>       folder[$name as string, $bookmarks as bookmarkd*] -> REPLACE $sname WITH $name; REPLACE $sbookmarks WITH $bookmarks
   BiGUL:
>    Rearr RVar (EDir DVar) (
>          CaseV [
>            CaseVBranch (PLeft (POut PVar)) (t(u1)),
>            CaseVBranch (PRight (POut (PProd PVar PVar)))
>                        (Rearr (RProd RVar RVar) (EProd (EDir ELeft) (EDir ERight)) (Update (UProd Replace Replace)))
                         (Update (UProd (UVar (Rearr (RRight (..)) (EDir (...)) (Replace))) (UVar ()))) --如果在caseV前面有source pat把source拆开了，那么需要pass到here再做真正的更新
>          ]
>    )
   If the pat is like this :
>       folder[$name as string, $bookmarks as bookmarkd+] -> u2
   the same.

E9. Where Bind
   BiFlux:
>    LET ($v1 as v:a, $v2 as v:b) := $v IN REPLACE $s WITH $v1 WHERE $v2 := $v1
   BiGUL:
>   Rearr (RProd RVar RVar) (EProd (EDir (DLeft DVar) (EDir (DRight DVar))) (
>   (Dep (id) (Rearr (RVar) (EDir DVar) (Replace)))  
>   ))


E10. Procedure
   BiFlux:
>    StmtP Name [XQExpr]
   Procedure call:
>    u($s/a, $v)
>    PROCEDURE u($source as s:book, $view as v:book) = u1
   BiGUL:
>    Update (UProd (UVar (Rearr RVar (EDir DVar) (t(u1)))) 
>                  (UVar Skip))
!comment: write the bookmark example in bigul.




------------------------------------------------------------
In summary, there are three questions:
1. case source pattern evaluates to bool 
>   pat: dd[h3[$title AS String], $dl AS s:dl]
  since we have a source
>  evalPatToBool :: MonadError' ErrorInfo m => Expr -> s -> m Bool
   decompose s to match with the expr, if success, then return True, else False.
2. The creation of expression for unmatched view and Adaptive branch
>  CREATE VALUE <dd><h3/><dl/></dd>
> createTemplateSource :: MonadError' ErrorInfo m => Expr -> s -> m s

!comment: no Type s will be given !

3. recursive call
