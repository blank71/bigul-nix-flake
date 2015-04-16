data BiGUL = Fail
           | Skip
           | Replace -- id_lens: get is id, put ignore s
           | Rearr XQExpr BiGUL
           | Iter BiGUL -- map on list.
           | Align (s -> m Bool)
                   (s -> v -> m Bool)
                   BiGUL
                   (v -> m s)
                   (s -> m (Maybe s)) -- may have deletion on s.
           | CaseS [(s -> m Bool, Either (s -> m s) BiGUL)]
           | CaseV [(Pat, BiGUL)]
           | Update Pat
        deriving (Eq,Show)


data XQExpr = XQEmpty              -- ()
            | XQProd XQExpr XQExpr        -- e,e'
            | XQElem String XQExpr        -- n[e] when we construct an element we must put all attributes first and sorted
            | XQAttr String XQExpr        -- @n='e'
--            | XQString String          -- w
--            | XQVar XVar            -- x (any variable)
            | XQLet Pat XQExpr XQExpr      -- let x = e in e'
--            | XQBool Bool            -- true | false
            | XQIf XQExpr XQExpr XQExpr      -- if c then e else e'
            | XQBinOp XPath.Op XQExpr XQExpr  -- e ~~ e'
            | XQFor XVar XQExpr XQExpr      -- for x- \in e return e' (still for tree variables)
            | XQPath CPath            -- special case to consider core paths (since their implementation as core uXQ is very different)
  deriving (Eq,Show)

type XVar = String
