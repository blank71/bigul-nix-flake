module ListFoldVer where

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ExistentialQuantification, ScopedTypeVariables #-}

import ListStage1

import GHC.Generics
import Generics.BiGUL.AST
import Generics.BiGUL.TH
import Generics.BiGUL.Interpreter

import Language.Haskell.TH as TH hiding (Name)

import Data.Typeable
import Data.List (elemIndex, maximum)
import Data.Maybe (catMaybes)
import Data.List (find, delete)



-- get (lensFoldr (+) 0) [1,2,3,4]  ==  10
-- put (lensFoldr plusl) ([1,2,3], 0) 8 -> ([3,2,3], 0)
-- \([1,2,3],0) -> (1, ([2,3], 0))
-- get (Replace `Prod` lensFoldr bx) (1, ([2,3], 0)) == (1, 5)
-- put bx (1, 5) 8 = (3, 5)
-- put (Replace `Prod` lensFoldr bx) (1, ([2,3], 0)) (3, 5) == (3, put (lensFoldr bx) ([2,3], 0) 5 )
-- == ...
-- ==
-- Note: the get direction of lensFoldr is executed many times (as length of the source list). time complexity is quadratic.
-- (1, sum(2,3,4)) 12 = (1, 9) 12 = (3, 9)
-- (2, sum(3,4)) 9    = (2 , 7) 9 = (2, 7)
-- ...


-- put semantics. composition.
-- higher order function
-- linear time complexity fold


-- foldr ::   (a -> b -> b)   ->   b -> [a] -> b
-- lensFoldr :: (BiGUL (x, xs) result) -> (BiGUL ([x], e) result)
lensFoldr :: (BiGUL (a, b) b) -> (BiGUL ([a], b) b)
lensFoldr bx =
  Case  [ $(normalS [| \(s, e) -> length s == 0 |] ) $
            $(rearrV [| \v -> ((),v) |]) $
              $(update [p| ((),v ) |] [p| (_, v) |] [d| v = Replace |])
        , $(normalSV [p| _ |] [p| _ |] ) $
            $(rearrS [| \((x:xs), e) -> (x, (xs,e))  |])
              (Replace `Prod` lensFoldr bx)
              `Compose`
              bx
        ]


-- the wrong version but the same as List.foldr1.
lensFoldr1 :: (BiGUL (a, a) a) -> (BiGUL [a] a)
lensFoldr1 bx =
  Case  [ $(normalS [| \s -> length s == 1 |] ) $
            $(update [p| v |] [p| [v] |] [d| v = Replace |])
        , $(normalSV [p| _ |] [p| _ |] ) $
            $(rearrS [| \(x:xs) -> (x,xs)  |])
              (Replace `Prod` lensFoldr1 bx)
              `Compose`
              bx
        ]

-- correct version.
lensFoldr1C :: BiGUL a b -> BiGUL (a, b) b -> (BiGUL [a] b)
lensFoldr1C f bx =
  Case  [ $(normalS [| \s -> length s == 1 |] ) $
            $(update [p| v |] [p| [v] |] [d| v = f `Compose` Replace |])
        , $(normalSV [p| _ |] [p| _ |] ) $
            $(rearrS [| \(x:xs) -> (x,xs)  |])
              (Replace `Prod` lensFoldr1C f bx)
              `Compose`
              bx
        ]

-- works only when (length s == length v) holds
lensMap :: BiGUL a b -> BiGUL [a] [b]
lensMap bx = $(rearrS [| \s -> (s, []) |])
  (lensFoldr ($(rearrV [| \(v:vs) -> (v,vs) |]) $ bx `Prod` Replace))


lensFoldrMapFusion :: (BiGUL a c) -> (BiGUL (c, b) b) -> (BiGUL ([a], b) b)
lensFoldrMapFusion mapBX foldBx =
  Case  [ $(normalS [| \(s, e) -> length s == 0 |] ) $
            $(rearrV [| \v -> ((),v) |]) $
              $(update [p| ((),v ) |] [p| (_, v) |] [d| v = Replace |])
        , $(normalSV [p| _ |] [p| _ |] ) $
            $(rearrS [| \((x:xs), e) -> (x, (xs,e))  |])
              ((mapBX `Compose` Replace) `Prod` lensFoldrMapFusion mapBX foldBx)
              `Compose`
              foldBx
        ]

lensFoldr1MapFusion :: BiGUL a c -> BiGUL (c, c) c -> BiGUL [a] c
lensFoldr1MapFusion mapBX foldBX =
  Case  [ $(normalS [| \s -> length s == 1 |] ) $
            $(update [p| v |] [p| [v] |] [d| v = mapBX `Compose` Replace |])
        , $(normalSV [p| _ |] [p| _ |] ) $
            $(rearrS [| \(x:xs) -> (x, xs)  |])
              ((mapBX `Compose` Replace) `Prod` lensFoldr1MapFusion mapBX foldBX)
              `Compose`
              foldBX
        ]

--                       map ->  change the last element -> foldr  -> fused foldr
lensFoldr1CMapFusion :: BiGUL a c -> BiGUL c b -> BiGUL (c, b) b -> BiGUL [a] b
lensFoldr1CMapFusion mapBX f foldBX =
  Case  [ $(normalS [| \s -> length s == 1 |] ) $
            $(update [p| v |] [p| [v] |] [d| v = mapBX `Compose` f `Compose` Replace |])
        , $(normalSV [p| _ |] [p| _ |] ) $
            $(rearrS [| \(x:xs) -> (x, xs)  |])
              ((mapBX `Compose` Replace) `Prod` lensFoldr1CMapFusion mapBX f foldBX)
              `Compose`
              foldBX
        ]


lensMapMapFusion :: BiGUL a b -> BiGUL b c -> BiGUL [a] [c]
lensMapMapFusion bx1 bx2 = $(rearrS [| \s -> (s, []) |])
  (lensFoldr ($(rearrV [| \(v:vs) -> (v,vs) |]) $ (bx1 `Compose` bx2) `Prod` Replace))



lensHead :: BiGUL [a] a
lensHead = lensFoldr1 ($(update [p| v |] [p| (v,_) |] [d| v = Replace |]))


-- work with non-empty list
lensMinimum :: (Ord a) => BiGUL [a] a
lensMinimum = lensFoldr1 lensMinInner

lensMinInner :: (Ord a) => BiGUL (a, a) a
lensMinInner =
  Case  [ $(normal [| \(elem, acc) v -> elem <= acc && v < acc |] ) $
            $(rearrV [| \v -> (v,()) |]) $
              Replace `Prod` Skip
        , $(normal [| \(elem, acc) v -> elem > acc && elem > v |] ) $
            $(rearrV [| \v -> ((),v) |]) $
              Skip `Prod` Replace
        , $(normal [| \ _ _ -> True |] ) (Fail "Possible reason: the view is larger than the second least elements in source")
        ]

-- work with non-empty list
lensMaximum :: (Ord a) => BiGUL [a] a
lensMaximum = lensFoldr1 lensMaxInner

lensMaxInner :: (Ord a) => BiGUL (a, a) a
lensMaxInner =
  Case  [ $(normal [| \(elem, acc) v -> elem >= acc && v > acc |] ) $
            $(rearrV [| \v -> (v,()) |]) $
              Replace `Prod` Skip
        , $(normal [| \(elem, acc) v -> elem < acc && v > elem |] ) $
            $(rearrV [| \v -> ((),v) |]) $
              Skip `Prod` Replace
        , $(normal [| \ _ _ -> True |] ) (Fail "Possible reason: the view is less than the second largest elements in source")
        ]


-- adaptive is used for reshaping source.
-- initial value
-- (rearranged)source ( 1 , [[2,3,4],[3,4],[4],[]] )
-- view       [[1,2,3,4],[2,3,4],[3,4],[4],[]]
lensTails :: Eq a => BiGUL [a] [[a]]
lensTails =
  Case  [ $(adaptive  [| \s v -> isTails v && length s /= length v - 1 |]) (\_ v -> replicate (length v - 1) undefined)
        , $(normalSV [p| _ |] [p| _ |] ) $
            $(rearrS [| \s -> (s,[[]]) |]) $
              lensFoldr xd
        ]
  where
    xd :: Eq a => BiGUL (a,[[a]]) [[a]]
    xd = $(rearrS [| \(s, t:ts) -> (s:t, t:ts) |])
            $(update [p| v:vs |] [p| (v, vs) |] [d| v = Replace ; vs = Replace |])


-- initial value
-- (rearranged)source ( 1, [[],[2],[2,3],[2,3,4]] ) -> ([ [], [1],[2],[2,3],[2,3,4]] )
-- view       [[],[1],[1,2],[1,2,3],[1,2,3,4]]
lensInits :: Eq a => BiGUL [a] [[a]]
lensInits =
  Case  [ $(adaptive  [| \s v -> isInits v && length s /= length v - 1 |]) (\_ v -> replicate (length v - 1) undefined)
        , $(normalSV [p| _ |] [p| _ |] ) $
            $(rearrS [| \s -> (s, [[]]) |]) (lensFoldr xd)
        ]
  where
    -- seperate three conditions into two functions for simplicity
    -- the view has one more element thant the source. so the first function handle the first element in the view, which is always an empty list ([]).
    -- after that, pass the remaining data to the second function.
    xd :: Eq a => BiGUL (a, [[a]]) [[a]]
    xd =
      Case  [ $(normalSV [p| (_, []:_) |] [p| []:_ |] ) $ -- view is [[],[1],[1,2] ...] there is at least one element, and the first element is []
                $(update [p| ([]:vs) |] [p| vs |] [d| vs = xd1 |])
            ]
    xd1 :: Eq a => BiGUL (a, [[a]]) [[a]]
    xd1 =
      Case  [ $(normalSV [p| (_, [_]) |] [p| [_:_] |] ) $ -- there is only one element left.
                $(rearrS [| \(s, [t]) -> s:t |]) $        -- ( 1, [[2,3,4]] )  --> 1:[2,3,4]
                  $(rearrV [| \[v] -> v |]) $             -- [[1,2,3,4]]       --> [1,2,3,4]
                    Replace

            , $(normal' [| \s v -> case (s, v) of ( (_, _:_) , (_:_):_) -> True; _ -> False |] [p| (_, _:_:_) |]) $
                $(rearrS [| \(s, t:ts) -> (s:t, (s,ts) ) |]) $ -- ( 1, [[],[2],[2,3],[2,3,4]] )  --> ( 1:[], (1, [[2],[2,3],[2,3,4]]) )
                  $(rearrV [| \(v:vs) -> (v,vs) |]) $          -- [[1],[1,2],[1,2,3],[1,2,3,4]]  --> ([1]  , [[1,2],[1,2,3],[1,2,3,4]])
                    Replace `Prod` xd1
            ]



-- compose hell. I am not clear about the put semantics ... and the time complexity
lensScanr :: (Eq b) => (BiGUL (a, b) b) -> (BiGUL ([a], b) [b])
lensScanr bx =
  Case  [ $(normalS [| \(s, e) -> length s == 0 |] ) $
            $(rearrV [| \[v] -> ((),v) |]) $
              $(update [p| ((),v ) |] [p| (_, v) |] [d| v = Replace |])
        , $(normalSV [p| _ |] [p| _ |] ) $
            $(rearrS [| \((x:xs), e) -> (x, (xs,e))  |]) $
              (((Replace `Prod` lensScanr bx) -- source (x, xs) --> (x, done)
                  `Compose`
                    $(rearrS [| \(a, b) -> (a, (b, b))  |]) (Replace `Prod` lensHead `Prod` Replace)) -- (x, (done, done)) --> (x, (head done, done))
                      `Compose`
                      $(rearrS [| \(a, (hb, b)) -> ((a, hb), b)  |]) (bx `Prod` Replace)) -- ((x, head done), done) --> (f x (head done), done)
                        `Compose`
                        lensCons -- f x (head done) : done
        ]


----------------------
t10g = get ((lensMap uleft) `Compose` lensMaximum) [Left 2, Left 7, Left 5]
t10p = put ((lensMap uleft) `Compose` lensMaximum) [Left 2, Left 7, Left 5] 999

t11g = get (lensFoldr1MapFusion uleft lensMaxInner) [Left 2, Left 7, Left 5]
t11p = put (lensFoldr1MapFusion uleft lensMaxInner) [Left 2, Left 7, Left 5] 999


-- map, map, foldr1,
t12g = get (lensMap (lensMap uleft) `Compose` lensMap lensMaximum `Compose` lensFoldr1 lensHead_test)
           ([[Left 1, Left 3, Left 2], [Left 6, Left 4, Left 5]])
t12p = put (lensMap (lensMap uleft) `Compose` lensMap lensMaximum `Compose` lensFoldr1 lensHead_test)
           ([[Left 1, Left 3, Left 2], [Left 6, Left 4, Left 5]])  999

-- map map fusion
t13g = get ( lensMap (lensMap uleft `Compose` lensMaximum) `Compose` lensFoldr1 lensHead_test)
           ([[Left 1, Left 3, Left 2], [Left 6, Left 4, Left 5]])
t13p = put ( lensMap (lensMap uleft `Compose` lensMaximum) `Compose` lensFoldr1 lensHead_test)
           ([[Left 1, Left 3, Left 2], [Left 6, Left 4, Left 5]]) 999

-- map fold fusion
t14g = get ( lensFoldr1MapFusion (lensMap uleft `Compose` lensMaximum) lensHead_test)
           ([[Left 1, Left 3, Left 2], [Left 6, Left 4, Left 5]])
t14p = put ( lensFoldr1MapFusion (lensMap uleft `Compose` lensMaximum) lensHead_test)
           ([[Left 1, Left 3, Left 2], [Left 6, Left 4, Left 5]]) 999

lensHead_test = ($(update [p| v |] [p| (v,_) |] [d| v = Replace |]))



uleft :: BiGUL (Either a b) a
uleft = $(update [p| x |] [p| Left x |] [d| x = Replace |])

