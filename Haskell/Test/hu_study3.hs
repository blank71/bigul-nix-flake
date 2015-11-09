{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{- Studying notes by Zhenjiang Hu @ 23/09/2015
   This note demonstates definitions of interesting put lenses
   over pairs and lists.
-}

import GHC.Generics
import Generics.BiGUL
import Util
import Generics.BiGUL.AST
import Language.Haskell.TH as TH
import Generics.BiGUL.TH

-- upFst:
--  (a,b) <-> a
upFst :: Eq a => BiGUL m (a,b) a
--upFst = Rearr RVar (EDir DVar `EProd` EConst ())
--                   (Update (UVar Replace `UProd` UVar Skip))

upFst = $(rearr [| \x -> (x,()) |]) $(update [p| (x,_) |] [d| x = Replace |])

{-

*Main> testGet upFst (1,2)
Right 1
*Main> testPut upFst (1,2) 100
Right (100,2)

-}

-- upSnd:
--  (a,b) <-> b
upSnd :: Eq b => BiGUL m (a,b) b
--upSnd = Rearr RVar (EConst () `EProd` EDir DVar)
--                   (Update (UVar Skip `UProd` UVar Replace))

upSnd = $(rearr [|  \x -> ((),x) |]) $(update [p| (_,x) |] [d| x = Replace |])

{-

*Main> testGet upSnd (1,2)
Right 2
*Main> testPut upSnd (1,2) 200
Right (1,200)

-}

upSwap :: (Eq a, Eq b) => BiGUL m (a,b) (b,a)
--upSwap = Rearr (RVar `RProd` RVar) (EDir (DRight DVar) `EProd` EDir (DLeft DVar)) Replace

upSwap = $(rearr [| \(x,y) -> (y,x) |]) Replace

{-

*Main> testGet upSwap (1,2)
Right (2,1)
*Main> testPut upSwap (1,2) (200,100)
Right (100,200)

-}

-- upHead
-- [100,2,3,4] <-> 100

upHead :: (Eq a, MonadError' ErrorInfo m) => BiGUL m [a] a
--upHead = CaseS [ (return . (==[]), Normal $ failMsg "upHead: the source should not be empty"),
--                 (return . (/=[]), Normal $ (Update (UElem (UVar Replace) (UVar Skip)) @@ upFst)) ]

upHead = CaseS [ $(normal [p| [] |]) $ failMsg "upHead: the source should not be empty",
                 $(normal' [| (/=[]) |])  ($(update [p| x:_ |] [d| x = Replace |]) @@ upFst) ]

{-

*Main> testGet upHead [1,2,3]
Right 1
*Main> testPut upHead [1,2,3] 100
Right [100,2,3]
*Main> testPut upHead [] 100
Left (ErrorInfo "upHead: the source should not be empty")

-}

upTail :: (Eq a, MonadError' ErrorInfo m) => BiGUL m [a] [a]
--upTail = CaseS [ (return . (==[]), Normal $ failMsg "upTail: the source should not be empty"),
--                 (return . (/=[]), Normal $ (Update (UElem (UVar Skip) (UVar Replace)) @@ upSnd)) ]
upTail = CaseS [ $(normal [p| [] |]) $ failMsg "upTail: the source should not be empty",
                 $(normal' [| (/=[]) |])  ($(update [p| _:x |] [d| x = Replace |]) @@ upSnd) ]
{-

*Main> testGet upTail [1,2,3]
Right [2,3]
*Main> testPut upTail [1,2,3] [100,200,300]
Right [1,100,200,300]

-}


-- mapU upHead:
--   [[1,2,3],[10,11,12,13],[20]] <-> [1,10,20]

mapUpHead :: MonadError' ErrorInfo m => BiGUL m [[Int]] [Int]
mapUpHead = mapU [0] upHead

{-

*Main> testGet mapUpHead [[1,2,3],[10,11,12,13],[20]]
Right [1,10,20]
*Main> testPut mapUpHead [[1,2,3],[10,11,12,13],[20]] [100,200,300]
Right [[100,2,3],[200,11,12,13],[300]]
*Main> testPut mapUpHead [[1,2,3],[10,11,12,13],[20]] [100,200,300,400]
Right [[100,2,3],[200,11,12,13],[300],[400]]
*Main> testPut mapUpHead [[1,2,3],[10,11,12,13],[20]] [100,200]
Right [[100,2,3],[200,11,12,13]]

-}



-- embedAt 2:
--  [1,2,300,4] <--> 300

embedAt :: (Eq a, MonadError' ErrorInfo m) => Int -> BiGUL m [a] a
embedAt i | i==0      = upHead
          | otherwise = upTail @@ embedAt (i-1)

{-

*Main> testGet (embedAt 3) [1..10]
Right 4
*Main> testPut (embedAt 3) [1..10] 100
Right [1,2,3,100,5,6,7,8,9,10]


-}

-- uLefts
--  [Left 1, Right 1, Left 3, Left 3, Right 2] <-> [Left 1, Left 3, Left 3]


--original uLefts
--uLefts :: (MonadError' ErrorInfo m, Eq a) => a -> BiGUL m [Either a a] [Either a a]
--uLefts a0 = CaseV [ CaseVBranch (PIn (PLeft (PConst ()))) $
--                      CaseS [ (return . all (not . isLeft), Normal Skip),
--                              (return . const True, Adaptive (\s v-> return (rmLefts s)))
--                            ],
--                    CaseVBranch (PIn (PRight (PProd PVar PVar))) $
--                      CaseS [ (\s -> return (s/=[] && hasLeftHead s),
--                                 Normal (Update (UElem (UVar Replace) (UVar (uLefts a0))))),
--                              (\s -> return (s/=[] && not (hasLeftHead s)),
--                                 Normal $ Rearr (RProd RVar RVar) (EProd (EConst ()) (EElem (EDir (DLeft DVar)) (EDir (DRight DVar))))
--                                                (Update (UElem (UVar Skip) (UVar (uLefts a0))))),
--                              (return . (==[]), Adaptive (\s -> return undefined))
--                            ]
--                  ]



uLefts :: (MonadError' ErrorInfo m, Eq a) => a -> BiGUL m [Either a a] [Either a a]
uLefts a0 = CaseV [ $(branch [p| [] |])  
                      ($(rearr [| \([]) -> () |])
                        (CaseS [ $(normal' [| all (not . isLeft) |]) Skip,
                                 $(adaptive [p| _ |]) (\s v-> return (rmLefts s))
                               ])),
                    $(branch [p| _ : _ |]) 
                      ($(rearr [| \(x:y) -> (x,y) |])
                        (CaseS [ $(normal [p| Left _ : _ |])
                                          $(update [p| x : xs |]
                                                   [d| x  = Replace
                                                       xs = uLefts a0 |]),
                                 $(normal [p| Right _ : _ |])
                                          ($(rearr [| \(x, xs) -> ((), x : xs) |])
                                           $(update [p| _ : xs |] [d| xs = uLefts a0 |])),
                                $(adaptive [p| [] |]) (\s v-> return [Left a0])
                              ]))
                  ]


hasLeftHead (Left _ : _) = True
hasLeftHead _ = False
rmLefts xs = [ x | x <- xs, not (isLeft x) ]
isLeft (Left _) = True
isLeft _ = False

{-

*Main> testGet (uLefts (-1)) [Left 1, Right 1, Left 3, Left 3, Right 2]
Right [Left 1,Left 3,Left 3]
*Main> testPut (uLefts (-1)) [Left 1, Right 1, Left 3, Left 3, Right 2] []
Right [Right 1,Right 2]
*Main> testPut (uLefts (-1)) [Left 1, Right 1, Left 3, Left 3, Right 2] [Left 100]
Right [Left 100,Right 1,Right 2]
*Main> testPut (uLefts (-1)) [Left 1, Right 1, Left 3, Left 3, Right 2] [Left 100, Left 200, Left 300, Left 400]
Right [Left 100,Right 1,Left 200,Left 300,Right 2,Left 400]

-}


-- rmLeftTags
--  [Left 1, Left 2, Left 3] <-> [1,2,3]

rmLeftTags :: (Eq a, MonadError' ErrorInfo m) => a -> BiGUL m [Either a a] [a]
rmLeftTags a = mapU (Left a) uLeft

uLeft :: (Eq a, MonadError' ErrorInfo m) => BiGUL m (Either a a) a
--uLeft = CaseS [ (return . isLeft,
--                   Normal $ Update (ULeft (UVar Replace))),
--                (return . const True,
--                   Normal $ failMsg "rmLeftTags: any element in the source should be a left value.")
--              ]

uLeft = CaseS [ $(normal' [| isLeft |]) $(update [p| Left x |] [d| x = Replace |]),
                $(normal [p| _ |]) $ failMsg "rmLeftTags: any element in the source should be a left value."
              ]

{-

*Main> testGet (rmLeftTags 0) [Left 1, Left 2, Left 3]
Right [1,2,3]
*Main> testGet (rmLeftTags 0) [Left 1, Left 2, Left 3, Right 4]
Left (ErrorInfo "failed.")
*Main> testPut (rmLeftTags 0) [Left 1, Left 2, Left 3] [10,20,30]
Right [Left 10,Left 20,Left 30]
*Main> testPut (rmLeftTags 0) [Left 1, Left 2, Left 3] [10,20,30,40]
Right [Left 10,Left 20,Left 30,Left 40]
*Main> testPut (rmLeftTags 0) [Left 1, Left 2, Left 3] [10,20]
Right [Left 10,Left 20]
*Main> testPut (rmLeftTags 0) [Left 1, Right 2, Left 3] [10,20]
Left (ErrorInfo "rmLeftTags: all elements in the source should be a left value.")

-}

