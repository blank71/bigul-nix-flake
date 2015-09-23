{- Studying notes by Zhenjiang Hu @ 23/09/2015 
   This note is to show how some new lenses can be defined in terms of 
   a pair of get and put. Certainly we should avoid using Emb
   to introduce new lenses when necessary as their well-behavedness 
   cannot be guaranteed.
-}

import Generics.BiGUL
import Util

-- unGrouping:
-- [("x",1),("y",10),("y",11),("x",2),("y",12)] <-> [("x",[1,2,12]),("y",[10,11,12])]

unGrouping :: (Eq a, Eq b, Monad m) => BiGUL m [(a,b)] [(a,[b])]
unGrouping = Emb (liftR1 get) (liftR2 put)
  where 
    get [] = []
    get ((a,b):xs) = (a, b : [b' | (a',b') <- xs, a'==a]) 
                     : get [ (a',b') | (a',b') <- xs, a'/=a]
    put s [] = []
    put [] ((a,bs):vs) = [(a,b) | b<-bs] ++ put [] vs
    put ((a,b):ss) vs | a `elem` dom vs = let (b',vs') = split a vs
                                          in (a,b') : put ss vs'
                      | otherwise       = put ss vs
    dom vs = [ a | (a,_) <- vs ]
    split a (v@(a',b':bs'):vs) | a==a'     = if bs'==[] then (b',vs) else (b',(a',bs'):vs)
                               | otherwise = let (b'',vs') = split a vs 
                                             in (b'',v:vs')

liftR1 :: Monad m => (a -> b) -> (a -> m b)
liftR1 f a = return (f a)

liftR2 :: Monad m => (a -> b -> c) -> (a -> b -> m c)
liftR2 f a b = return (f a b)

{-

*Main> testGet unGrouping [("x",1),("y",10),("y",11),("x",2),("y",12)]
Right [("x",[1,2]),("y",[10,11,12])]
*Main> testPut unGrouping [("x",1),("y",10),("y",11),("x",2),("y",12)] [("x",[1,2]),("y",[10,11,12])]
Right [("x",1),("y",10),("y",11),("x",2),("y",12)]
*Main> testPut unGrouping [("x",1),("y",10),("y",11),("x",2),("y",12)] [("x",[1,3]),("y",[10,11,12])]
Right [("x",1),("y",10),("y",11),("x",3),("y",12)]
*Main> testPut unGrouping [("x",1),("y",10),("y",11),("x",2),("y",12)] [("x",[1,3]),("y",[10,11])]
Right [("x",1),("y",10),("y",11),("x",3)]
*Main> testPut unGrouping [("x",1),("y",10),("y",11),("x",2),("y",12)] [("x",[1,3]),("y",[100,11])]
Right [("x",1),("y",100),("y",11),("x",3)]

-}

-- Another example is the lens composition (@@) as defined in Util.hs.

