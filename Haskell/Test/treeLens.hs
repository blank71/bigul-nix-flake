{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}


import GHC.Generics
import Generics.BiGUL
import Util
import Generics.BiGUL.AST
import Language.Haskell.TH as TH hiding (Name)
import Generics.BiGUL.TH
import Data.Set

type Name = String
data NTree = Branchs [(Name,NTree)] deriving(Eq,Show)
deriveBiGULGeneric ''NTree

hoist :: MonadError' ErrorInfo m => Name -> BiGUL m NTree NTree
hoist name = Rearr RVar  (EIn (EIn (ERight
                          (EProd
                           (EProd (EConst name) (EDir DVar)) (EIn (ELeft (EConst ()))))))) Replace

plunge :: MonadError' ErrorInfo m => Name -> BiGUL m NTree NTree
plunge name = Rearr (RIn (RIn (RRight (RProd (RProd (RConst name) RVar) (RIn (RLeft (RConst ())))))))
                    (EDir (DLeft (DRight DVar)))
                    Replace


inner :: MonadError' ErrorInfo m => Name -> Name -> BiGUL m [(Name, NTree)] [(Name, NTree)]
inner n1 n2 = Compose (Rearr RVar  (EIn (ERight
                          (EProd
                           (EProd (EConst n1) (EDir DVar)) (EIn (ELeft (EConst ())))))) Replace)
                      (Rearr (RIn (RRight (RProd (RProd (RConst n2) RVar) (RIn (RLeft (RConst ()))))))
                          (EDir (DLeft (DRight DVar)))
                           Replace)

rename :: MonadError' ErrorInfo m => Name -> Name -> BiGUL m NTree NTree
rename n1 n2 = $(rearr [| \(Branchs bs) -> bs |])
               ($(update [p| Branchs bs |]
                         [d| bs = Xfork (\(n,_) -> return (n1 == n))
                                        (\(n,_) -> return (n2 == n))
                                        (inner n1 n2)
                                        Replace |]))

xconst :: (Eq a,Show a,MonadError' ErrorInfo m) => a -> BiGUL m s a
xconst val = Rearr (RConst val)
                   (EConst ())
                   Skip

xfilter :: MonadError' ErrorInfo m => Set Name -> BiGUL m NTree NTree
xfilter names = $(rearr [| \(Branchs bs) -> bs |])
                ($(update [p| Branchs bs |]
                          [d| bs = Xfork (\(n,_) -> return (member n names))
                                         (\(n,_) -> return (member n names))
                                         Replace
                                         (xconst [])|]))

xprune :: MonadError' ErrorInfo m => Name -> BiGUL m NTree NTree
xprune  name = $(rearr [| \(Branchs bs) -> bs |])
                ($(update [p| Branchs bs |]
                          [d| bs = Xfork (\(n,_) -> return (n == name))
                                         (\(n,_) -> return (n == name))
                                         (xconst [])
                                         Replace|]))


xadd :: MonadError' ErrorInfo m => Name -> NTree -> BiGUL m NTree NTree
xadd name tree = $(rearr [| \(Branchs bs) -> bs |])
                 ($(update [p| Branchs bs |]
                           [d| bs = Xfork (\_ -> return False)
                                          (\(n,_) -> return (n == name))
                                          (xconst [(name,tree)])
                                          Replace|]))

xfocus :: MonadError' ErrorInfo m => Name -> BiGUL m NTree NTree
xfocus name = Compose (xfilter (singleton name)) (hoist name)


inner2 :: MonadError' ErrorInfo m => Name -> BiGUL m [(Name, NTree)] [(Name, NTree)]
inner2 name  = Rearr RVar (EIn (ERight
                          (EProd
                           (EProd (EConst name) (EIn (EDir DVar))) (EIn (ELeft (EConst ())))))) Replace

hoistNonunique :: MonadError' ErrorInfo m => Name -> Set Name -> BiGUL m NTree NTree
hoistNonunique name names =  $(rearr [| \(Branchs bs) -> bs |])
                              ($(update [p| Branchs bs |]
                                        [d| bs = Xfork (\(n,_) -> return (n == name))
                                                       (\(n,_) -> return (member n names))
                                                       (inner2 name)
                                                       Replace|]))

xmap :: MonadError' ErrorInfo m => BiGUL m NTree NTree -> BiGUL m NTree NTree
xmap bigul = $(rearr [| \(Branchs bs) -> bs |])
             ($(update [p| Branchs bs |]
                       [d| bs = Align (\_ -> return True)
                                      (\(names,_) (namev,_) -> return (names == namev))
                                      $(update [p| (n,tree) |]
                                               [d| n = Replace ; tree = bigul|])
                                      (\_ -> return ("",(Branchs [])))
                                      (\_ -> return Nothing)|]))



wmap :: MonadError' ErrorInfo m => BiGUL m (Name,NTree) (Name,NTree) -> BiGUL m NTree NTree
wmap bigul = $(rearr [| \(Branchs bs) -> bs |])
             ($(update [p| Branchs bs |]
                       [d| bs = Align (\_ -> return True)
                                      (\(names,_) (namev,_) -> return (names == namev))
                                      bigul
                                      (\_ -> return ("",(Branchs [])))
                                      (\_ -> return Nothing)|]))


list2NTree :: [Name] -> NTree
list2NTree []     = Branchs []
list2NTree (x:xs) = Branchs [("hd", Branchs [(x,Branchs [])]) , ("tl", list2NTree xs)]

nTree2List :: NTree -> [Name]
nTree2List (Branchs []) = []
nTree2List (Branchs [("hd", Branchs [(x,Branchs [])]),("tl", tltree)]) = x:(nTree2List tltree)
nTree2List _ = ["Invalid NTree to list"]

xhd :: MonadError' ErrorInfo m => BiGUL m NTree NTree
xhd = xfocus "hd"

xtl :: MonadError' ErrorInfo m => BiGUL m NTree NTree
xtl = xfocus "tl"

list_map :: MonadError' ErrorInfo m => BiGUL m NTree NTree -> BiGUL m NTree NTree
list_map bigul = wmap (CaseV [ $(branch [p|("hd",_)|]) $(update [p| (n,tree) |]
                                                                [d| n = Replace ; tree = bigul|]),
                               $(branch [p|("tl",_)|]) $(update [p| (n,tree) |]
                                                                [d| n = Replace ; tree = list_map bigul|])
                             ])

inner3 :: MonadError' ErrorInfo m =>  BiGUL m [(Name, NTree)] NTree
inner3  = $(rearr [| \(Branchs bs) -> bs |]) $
          Xfork (\(n,_) -> return ("tmp" == n))
                (\(n,_) -> return ("hd" == n))
                (inner "tmp" "hd")
                Replace

inner4 :: MonadError' ErrorInfo m =>  BiGUL m NTree [(Name, NTree)]
inner4 = Rearr (RIn (RRight (RProd (RProd (RConst "tl") RVar) (RIn (RLeft (RConst ()))))))
                    (EDir (DLeft (DRight DVar)))
                    Replace

xrotate :: MonadError' ErrorInfo m => BiGUL m NTree NTree
xrotate = CaseS [$(normal [p| Branchs [] |]) Replace,
                 $(normal [p| Branchs [("hd",_),("tl",Branchs [])]|]) Replace,
                 $(normal [p| _ |]) (Compose (rename "hd" "tmp")
                                             (Compose (hoistNonunique "tl" (fromList ["hd","tl"]))
                                             ($(rearr [| \(Branchs bs) -> bs |])
                                              ($(update [p| Branchs bs |]
                                                        [d| bs = Xfork (\(n,_) -> return (n == "hd"))
                                                                       (\(n,_) -> return (n == "hd"))
                                                                       Replace
                                                                       (Compose inner3
                                                                                (Compose xrotate
                                                                                inner4)) |])))))]

list_reverse :: MonadError' ErrorInfo m => BiGUL m NTree NTree
list_reverse =  Compose (wmap (CaseV [$(branch [p| ("hd",_) |]) Replace,
                                      $(branch [p| ("tl",_) |]) $(update [p| (tlr,tree) |] [d| tlr = Replace ; tree = list_reverse |])]))
                        xrotate
