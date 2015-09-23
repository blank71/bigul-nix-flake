{-# LANGUAGE FlexibleContexts #-}
{- Studying notes by Zhenjiang Hu @ 23/09/2015
   Define a set of higher order functions for gluing smaller lenses.
   It is hoped that these higher order functions can help hide the
   lower level stuffs of pattern matching.
-}

import Generics.BiGUL
import Util

-- product

uFst :: Eq c => BiGUL m a c -> BiGUL m (a,b) c
uFst u = Rearr RVar (EDir DVar `EProd` EConst ())
                    (Update (UVar u `UProd` UVar Skip))

uSnd :: Eq c => BiGUL m b c -> BiGUL m (a,b) c
uSnd u = Rearr RVar (EConst () `EProd` EDir DVar)
                    (Update (UVar Skip `UProd` UVar u))

uProd :: BiGUL m a c -> BiGUL m b d -> BiGUL m (a,b) (c,d)
uProd u1 u2 = Update (UVar u1 `UProd` UVar u2)

uSplit :: (Eq c, MonadError' ErrorInfo m) => BiGUL m a c -> BiGUL m b c -> BiGUL m (a,b) c
uSplit u1 u2 = uProd u1 u2 @@ uDup

uDup :: (Eq a, MonadError' ErrorInfo m) => BiGUL m (a,a) a
uDup = CaseS [ (\(s1,s2) -> return (s1==s2), 
                 Normal $ Rearr RVar (EDir DVar `EProd` EDir DVar)
                                     (Update (UVar Replace `UProd` UVar Replace))),
               (return . const True, 
                 Normal $ failMsg "uDup: the source should be a pair of equivalent values")
             ]

-- sum

uLeft :: (Eq a, MonadError' ErrorInfo m) => BiGUL m a c -> BiGUL m (Either a b) c
uLeft u = CaseS [ (return . isLeft, 
                     Normal $ Update (ULeft (UVar u))),
                  (return . const True, 
                     Normal $ failMsg "uLeft: any element in the source should be a left value.")
                ]

isLeft (Left _) = True
isLeft _ = False

uRight :: (Eq b, MonadError' ErrorInfo m) => BiGUL m b c -> BiGUL m (Either a b) c
uRight u = CaseS [ (return . isRight, 
                     Normal $ Update (URight (UVar u))),
                  (return . const True, 
                     Normal $ failMsg "uRight: any element in the source should be a right value.")
                ]

isRight (Right _) = True
isRight _ = False

uSum :: (Eq a, Eq b, MonadError' ErrorInfo m) => BiGUL m a c -> BiGUL m b d -> BiGUL m (Either a b) (Either c d)
uSum u1 u2 = CaseV [ CaseVBranch (PLeft PVar) $ uLeft u1,
                     CaseVBranch (PRight PVar) $ uRight u2 
                   ]

-- more for sum ...
        
-- list folds on S and  V

-- caseListS :: BiGUL m [] v -> BiGUL m (a,[a]) v -> BiFUL m [a] 