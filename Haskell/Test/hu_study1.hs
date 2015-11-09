{- Studying notes by Zhenjiang Hu @ 22/09/2015
   It would be better to read this together with the paper
   submitted to PEPM'16 .
-}
import GHC.Generics
import Generics.BiGUL
import Generics.BiGUL.AST
import Language.Haskell.TH as TH hiding(Name)
import Generics.BiGUL.TH
-----------------------------------------------
--  Test on basic combinators of BiGul
-----------------------------------------------

-- We prepare two simpler functions for testing put/get of
-- a bigul lens; it will give the result if it succeeds and
-- shows an error message if it fails.

testPut :: BiGUL (Either ErrorInfo) s v -> s -> v -> Either ErrorInfo s
testPut u s v = catchBind (put u s v) (\s' -> Right s') (\e -> Left e)

testGet :: BiGUL (Either ErrorInfo) s v -> s -> Either ErrorInfo v
testGet u s = catchBind (get u s) (\v' -> Right v') (\e -> Left e)

---------------------------------
-- testing Fail, Skip and Replace
---------------------------------

{-

*Main> testGet Fail 1
Left (ErrorInfo "get failed")
*Main> testPut Fail 1 2
Left (ErrorInfo "update fails")

*Main> testGet Skip 1
Right ()
*Main> testPut Skip 1 ()
Right 1

Note that the view of Skip should be ().

*Main> testGet Replace 1
Right 1
*Main> testPut Replace 1 2
Right 2

-}

---------------------------------
-- testing source update: Update
---------------------------------

--upat1 = UVar Replace `UProd` UVar Skip
--update1 = Update upat1
update1 = $(update [p| (x,_) |] [d| x = Replace |])


{-

*Main> testGet update1 (1,2)
Right (1,())
*Main> testPut update1 (1,2) (100,())
Right (100,2)

-}

-- UProd is left associative
--upat2 = UVar Replace `UProd` UVar Skip `UProd` UVar Skip
--update2 = Update upat2

-- (x,_ ,_ ...) in new syntax is right associative by default
update2 = $(update [p| ((x,_),_) |] [d| x = Replace |])

{-

*Main> testGet update2 ((1,2),3)
Right ((1,()),())
*Main> testPut update2 ((1,2),3) ((100,()),())
Right ((100,2),3)

-}

--upat3 = ULeft upat1
--update3 = Update upat3

-- !!!!!!!!! if you use data constructors , you need add type declaration explicitly
update3 :: BiGUL m (Either (a,b) c) (a,())
update3 = $(update [p| Left (x,_) |] [d| x = Replace|])

{-

*Main> testGet update3 (Left (1,2))
Right (1,())
*Main> testPut update3 (Left (1,2)) (100,())
Right (Left (100,2))

*Main> testGet update3 (right (1,2))
<interactive>:66:18: Not in scope: ‘right’
*Main> testGet update3 (Right (1,2))
Left (ErrorInfo "ULeft pat not match")

-}

-- testing on other cases

{-

*Main> testGet (Update (UConst 5)) 5
Right ()
*Main> testPut (Update (UConst 5)) 5 ()
Right 5

*Main> testGet (Update (UConst 5)) 1
Left (ErrorInfo "source is not a constant.")

*Main> testGet (Update (UElem (UVar Replace) (UVar Replace))) [1,2,3]
Right (1,[2,3])
*Main> testPut (Update (UElem (UVar Replace) (UVar Replace))) [1,2,3] (100,[200,300])
Right [100,200,300]

*Main> testPut (Update (UElem (UVar Replace) (UVar Replace))) [1,2,3] (100,[200,300,400])
Right [100,200,300,400]



*Main> testGet  $(update [p| 5 |] [d| |]) 5
Right ()
*Main> testPut  $(update [p| 5 |] [d| |]) 5 ()
Right 5

*Main> testGet  $(update [p| 5 |] [d| |]) 1
Left (ErrorInfo "source is not a constant.")

*Main> testGet  $(update [p| x:xs |] [d| x = Replace; xs = Replace |]) [1,2,3]
Right (1,[2,3])
*Main> testPut  $(update [p| x:xs |] [d| x = Replace; xs = Replace |]) [1,2,3] (100,[200,300])
Right [100,200,300]

*Main> testPut  $(update [p| x:xs |] [d| x = Replace; xs = Replace |]) [1,2,3] (100,[200,300,400])
Right [100,200,300,400]
-}

-- Question: Why UOut is necessary?

---------------------------------------------------
-- testing view arrangement: Rearr
--   rearrange the view of pattern RPat to an intermediate
--   view of pattern EPat and then apply the lens between
--   the soruce and the intemediate view.
---------------------------------------------------

rearr1 :: (Eq a0, Eq b0) => BiGUL m (b0, a0) (a0, b0)
--rearr1 = Rearr rp1 ep1 Replace
--  where
--    rp1 = RVar `RProd` RVar
--    ep1 = EDir (DRight DVar) `EProd` EDir (DLeft DVar)

rearr1 = $(rearr [| \(x,y) -> (y,x) |]) Replace

{-

*Main> testGet rearr1 (1,2)
Right (2,1)
*Main> testPut rearr1 (1,2) (100,200)
Right (200,100)

-}

rearr2 :: (Eq a0, Eq b0) => BiGUL m ((b0, ()), a0) (a0, b0)
--rearr2 = Rearr rp1 ep2 Replace
--  where
--    rp1 = RVar `RProd` RVar
--    ep2 = (EDir (DRight DVar) `EProd` EConst ()) `EProd` EDir (DLeft DVar)
    -- u = Update ((UVar Replace `UProd` UVar Skip) `UProd` UVar Replace)

rearr2 = $(rearr [| \(x,y) -> ((y,()),x)|]) $(update [p| ((x,_),y) |] [d| x = Replace ; y = Replace|])

{-

*Main> testGet rearr2 ((1,()),2)
Right (2,1)
*Main> testPut rearr2 ((1,()),2) (100,200)
Right ((200,()),100)

-}

-- Todo: to test RElem, EElem, ECompare

---------------------------------------
-- Testing dependency in the view: Dep
---------------------------------------

dep1 :: BiGUL m Int (Int, Int)
dep1 = Dep (\v -> v+1) Replace

{-

*Main> testPut dep1 5 (5,6)
Right 5
*Main> testPut dep1 5 (10,11)
Right 10

*Main> testPut dep1 5 (5,10)
Left (ErrorInfo "view dependency not match")

-}

-----------------------------------------
-- Testing analysis on the soruce: CaseS
-----------------------------------------

cases1 :: Monad m => BiGUL m Int Int
--cases1 = CaseS [ (return . (>=100), Normal $ Fail),
--                 (return . (\s -> s>=0 && s<100), Normal Replace),
--                 (return . (<0), Adaptive (\s v -> return (-s))) ]

cases1 = CaseS [ $(normal' [| \s -> s>=100 |]) Fail,
                 $(normal' [| \s -> s>=0 && s<100 |]) Replace,
                 $(adaptive' [| \s -> s<0 |]) (\s v -> return (-s))
               ]

{-

*Main> testGet cases1 90
Right 90
*Main> testGet cases1 120
Left (ErrorInfo "get failed")
*Main> testGet cases1 (-10)
Left (ErrorInfo "Get: caseS shall not match adaptive branch")

*Main> testPut cases1 20 50
Right 50
*Main> testPut cases1 120 50
Left (ErrorInfo "update fails")
*Main> testPut cases1 (-12) 50
Right 50

-}

-- todo: test over lists or trees

---------------------------------------
-- testing analysis on the view: CaseV
---------------------------------------

casev1 :: (Eq b',Monad m) => BiGUL m (Either b' b) (Either b' ())
--casev1 = CaseV [
--           CaseVBranch (PLeft PVar)  $ Update (ULeft (UVar Replace)),
--           CaseVBranch (PRight PVar) $ Update (URight (UVar Skip))
--         ]
casev1 = CaseV [
            $(branch [p| Left _ |]) 
               ($(rearr [| \(Left x') -> x' |])
                     ($(update [p| Left x |] [d| x = Replace |]))),
            $(branch [p| Right _ |]) 
               ($(rearr [| \(Right y') -> y' |])
                     ($(update [p| Right _ |] [d| |])))
         ]

{-

*Main> testGet casev1 (Left 1)
Right (Left 1)
*Main> testPut casev1 (Left 1) (Left 100)
Right (Left 100)
*Main> testGet casev1 (Right 1)
Right (Right ())
*Main> testPut casev1 (Right 1) (Right ())
Right (Right 1)

-}

----------------------------------------
-- testing source-view alignment: Align
----------------------------------------

type Persons = [(Name, Salary)]
type Name = String
type Salary = Int

-- Suppose the view contains those persons
-- who have salary greater than 10.

align1 :: Monad m => BiGUL m [(String, Int)] [(String, Int)]
align1 = Align (\s -> return (salary s > 10))
               (\s v -> return (name s == name v))
               {- case matched -}  Replace
               {- case unmatchS -} return
               {- case unmatchV -} (\s -> return Nothing)
  where
    salary (n,s) = s
    name (n,s) = n

{-

*Main> testGet align1 [("a",1), ("b", 20)]
Right [("b",20)]
*Main> testPut align1 [("a",1), ("b", 20)] [("b",50), ("c",5)]
Left (ErrorInfo "created source not satisfy the source filter condition")
*Main> testPut align1 [("a",1), ("b", 20)] [("b",50), ("c",60)]
Right [("a",1),("b",50),("c",60)]
*Main> testPut align1 [("a",1), ("b", 20)] [("c",60)]
Right [("a",1),("c",60)]
*Main>

-}




