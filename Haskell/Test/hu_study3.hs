{-# LANGUAGE FlexibleContexts  #-}
{- Studying notes by Zhenjiang Hu @ 23/09/2015
   This note is to show how to define interesting put lenses over lists.
-}

import Generics.BiGUL
import Util

-- upFst:
--  (a,b) <-> a
upFst :: Eq a => BiGUL m (a,b) a
upFst = Rearr RVar (EDir DVar `EProd` EConst ())
                   (Update (UVar Replace `UProd` UVar Skip))

{-

*Main> testGet upFst (1,2)
Right 1
*Main> testPut upFst (1,2) 100
Right (100,2)

-}

-- upSnd:
--  (a,b) <-> b
upSnd :: Eq b => BiGUL m (a,b) b
upSnd = Rearr RVar (EConst () `EProd` EDir DVar)
                   (Update (UVar Skip `UProd` UVar Replace))

{-

*Main> testGet upSnd (1,2)
Right 2
*Main> testPut upSnd (1,2) 200
Right (1,200)

-}

upSwap :: (Eq a, Eq b) => BiGUL m (a,b) (b,a)
upSwap = Rearr (RVar `RProd` RVar) (EDir (DRight DVar) `EProd` EDir (DLeft DVar)) Replace

{-

*Main> testGet upSwap (1,2)
Right (2,1)
*Main> testPut upSwap (1,2) (200,100)
Right (100,200)

-}

-- upHead
-- [100,2,3,4] <-> 100

upHead :: (Eq a, MonadError' ErrorInfo m) => BiGUL m [a] a
upHead = CaseS [ (return . (==[]), Normal $ failMsg "upHead: the source should not be empty"),
                 (return . (/=[]), Normal $ (Update (UElem (UVar Replace) (UVar Skip)) @@ upFst)) ]

{-

*Main> testGet upHead [1,2,3]
Right 1
*Main> testPut upHead [1,2,3] 100
Right [100,2,3]
*Main> testPut upHead [] 100
Left (ErrorInfo "upHead: the source should not be empty")

-}

upTail :: (Eq a, MonadError' ErrorInfo m) => BiGUL m [a] [a]
upTail = CaseS [ (return . (==[]), Normal $ failMsg "upHead: the source should not be empty"),
                 (return . (/=[]), Normal $ (Update (UElem (UVar Skip) (UVar Replace)) @@ upSnd)) ]

{-

*Main> testGet upTail [1,2,3]
Right [2,3]
*Main> testPut upTail [1,2,3] [100,200,300]
Right [1,100,200,300]

-}

-- mapU upHead:
--   [[1,2,3],[10,11,12,13],[20]] <-> [1,10,20]

mapU :: (Eq s, Eq v, Monad m) => s -> BiGUL m s v -> BiGUL m [s] [v]
mapU s0 u = CaseV [ CaseVBranch (PConst []) $
                      CaseS [ (return . (==[]), Normal Skip),
                              (return . (/=[]), Adaptive (\s -> return []))
                            ],
                    CaseVBranch (PElem PVar PVar) $
                      CaseS [ (return . (/=[]), Normal (Update (UElem (UVar u) (UVar (mapU s0 u))))),
                              (return . (==[]), Adaptive (\s -> return [s0]))
                            ]
                  ]

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

-- type error ... ???
-- Qestion: how to write a put which applies a lens to the tail of a list
--          while keeping the first unchanged?

-- uLefts
--  [Left 1, Right 1, Left 3, Left 3, Right 2] <-> [Left 1, Left 3, Left 3]

uLefts :: (MonadError' ErrorInfo m, Eq a) => a -> BiGUL m [Either a a] [Either a a]
uLefts a0 = CaseV [ CaseVBranch (PConst []) $
                      CaseS [ (return . all (not . isLeft), Normal Skip),
                              (return . const True, Adaptive (\s -> return (rmLefts s)))
                            ],
                    CaseVBranch (PElem PVar PVar) $
                      CaseS [ (\s -> return (s/=[] && hasLeftHead s),
                                 Normal (Update (UElem (UVar Replace) (UVar (uLefts a0))))),
                              (\s -> return (s/=[] && not (hasLeftHead s)),
                                 Normal $ Rearr (RProd RVar RVar) (EProd (EConst ()) (EElem (EDir (DLeft DVar)) (EDir (DRight DVar))))
                                                (Update (UElem (UVar Skip) (UVar (uLefts a0))))),
                              (return . (==[]), Adaptive (\s -> return [Left a0]))
                            ]
                  ]
  where
    hasLeftHead (Left _ : _) = True
    hasLeftHead _ = False
    rmLefts xs = [ x | x <- xs, not (isLeft x) ]
    isLeft (Left _) = True
    isLeft _ = False

