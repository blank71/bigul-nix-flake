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

--import Data.Set
--import Control.Monad.Except

bHead  = get lensHead
bpHead = put lensHead

bLast  = get lensLast
bpLast = put lensLast

bTail  :: (Typeable a, Defaultable a) => [a] -> GetResult [a] [a]
bTail  = get lensTailNonStrict
bpTail :: (Typeable a, Defaultable a) => [a] -> [a] -> PutResult [a] [a]
bpTail = put lensTailNonStrict

bTail'  = get lensTailStrict
bpTail' = put lensTailStrict

bInit  :: (Typeable a, Defaultable a) => [a] -> GetResult [a] [a]
bInit  = get lensInitNonStrict
bpInit :: (Typeable a, Defaultable a) => [a] -> [a] -> PutResult [a] [a]
bpInit = put lensInitNonStrict

bInit'  = get lensInitStrict
bpInit' = put lensInitStrict

bNull  = get lensNull
bpNull = put lensNull

bLength  :: (Typeable a, Defaultable a) => [a] -> GetResult [a] Int
bLength  = get lengthEmb
bpLength :: (Typeable a, Defaultable a) => [a] -> Int -> PutResult [a] Int
bpLength = put lengthEmb

bLensDrop :: (Typeable a, Defaultable a) => Int -> [a] -> GetResult [a] [a]
bLensDrop n = get (lensDrop n)

bpLensDrop :: (Typeable a, Defaultable a) => Int -> [a] -> [a] -> PutResult [a] [a]
bpLensDrop n = put (lensDrop n)

bLensMaximum :: (Ord a) => [a] -> GetResult [a] a
bLensMaximum  = get lensMaximum

bpLensMaximum :: (Ord a) => [a] -> a -> PutResult [a] a
bpLensMaximum  = put lensMaximum


-- put semantics: replace the first element in list with the provided one
-- work only with non-empty list
lensHead :: BiGUL [a] a
lensHead = $(update [p| x |] [p| x:_ |]  [d| x = Replace |])

-- work only with non-empty list
lensLast :: BiGUL [a] a
lensLast = Case [$(normalS [p| [_] |])
                  $(update [p| x |] [p| x:[] |] [d| x = Replace  |])
              ,$(normalS [p| _:_ |])
                  $(update [p| x |] [p| _:x |] [d| x = lensLast |])  ]


-- giving a non-empty source list,
-- replace its tail list with a view list of any length
lensTailNonStrict :: (Typeable a, Defaultable a) => BiGUL [a] [a]
lensTailNonStrict = Case  [ $(adaptive [|\s v -> length s /= 1 + length v |])
                              (\s v ->  if length s > length v
                                          then drop (length s - (1 + length v)) s -- try to preserve the source (the rear part)
                                          else replicate (1 + length v) (defaultVal . show . typeOf $ s ))
                          , $(normalS [p| _:_ |])
                              $(update [p| x |] [p| _:x |] [d| x = replaceByPosition |])
                          , $(normalS [| null |])
                              (Fail "empty source list detected")
                          ]

-- given a non-empty source list of length n,
-- replace its tail list with a view list of length (n-1)
lensTailStrict :: BiGUL [a] [a]
lensTailStrict = Case [ $(normal [|\s v -> length s /= 1 + length v |])
                          (Fail "length mismatch")
                      , $(normalS [p| _:_ |])
                            $(update [p| x |] [p| _:x |] [d| x = replaceByPosition |])
                      , $(normalS [| null |])
                           (Fail "empty source list detected")
                      ]

lensInitNonStrict :: (Typeable a, Defaultable a) => BiGUL [a] [a]
lensInitNonStrict = Case  [ $(adaptive [|\s v -> length s /= 1 + length v |])
                                (\s v ->  if length s > length v
                                            then take (1 + length v) s -- try to preserve the source (the front part)
                                            else replicate (1 + length v) (defaultVal . show . typeOf $ s))
                          , $(normalSV [p| _:_ |] [p| _:_ |] )
                              $(update [p| x:xs |] [p| x:xs |] [d| x = Replace; xs = lensInitStrict |])
                          , $(normalSV [p| [_] |] [p| [] |] )
                              $(update [p| [] |] [p| [_] |] [d| |])
                          , $(normalS [| null |])
                               (Fail "empty source list detected")
                          ]


-- given a non-empty source list of length n,
-- replace its init list with a view list of length (n-1)
lensInitStrict  :: BiGUL [a] [a]
lensInitStrict = Case [ $(adaptive [|\s v -> length s /= 1 + length v |])
                        (\_ _ -> error "length mismatch")
                      , $(normalSV [p| _:_ |] [p| _:_ |] )
                            $(update [p| x:xs |] [p| x:xs |] [d| x = Replace; xs = lensInitStrict |])
                      , $(normalSV [p| [_] |] [p| [] |] )
                            $(update [p| [] |] [p| [_] |] [d| |])
                      , $(normalS [| null |])
                           (Fail "empty source list detected")
                      ]


lensNull :: BiGUL [a] Bool
lensNull = Case [$(normalSV [p| [] |] [p| True |]  ) $
                    $(rearrV [| \True -> () |])
                      $(update [p| () |] [p| _ |] [d|  |])
                , $(adaptiveSV [p| [] |] [p| False |] )
                    (\_ _ -> [undefined])
                , $(adaptiveSV [p| _:_ |] [p| True |] )
                    (\_ _ -> [])
                , $(normalSV [p| _:_ |] [p| False |] ) $
                    $(rearrV [| \False -> ()  |])
                      $(update [p| () |] [p| _ |] [d|  |])
                ]

lensLengthStrict :: BiGUL [a] Int
lensLengthStrict = Case [ $(normal [| \s v -> length s == v |] ) $
                            $(rearrV [| \v -> () |])
                              $(update [p| () |] [p| _ |] [d|  |])
                        , $(adaptive  [|\ _ _ -> True|])  (\_ _ -> error "length mismatch")]


-- put semantics : replace the first n elements of the source list
-- well-bahaved state consistency: length v <= n
-- parameters should satisfy either length s < n && length s == length v
-- or length s >= n && length v == n
lensTake :: Int -> BiGUL [a] [a]
lensTake n =
  Case  [ $(normal [| \s v -> let c1 = length s < n && length s == length v
                                  c2 = length s >= n && length v == n
                              in  not (c1 || c2) |])
            (Fail $ "parameters should satisfy either length s < n && length s == length v\n" ++ "or length s >= n && length v == n\n")  -- for PutGet:  get (take n) s (put (take n) s v)
        -- condition c1
        ,$(normal [| \s v -> length s == 0 && length v == 0 && n > 0 |]  ) $
            $(update [p| [] |] [p| [] |] [d|  |])
        -- condition c1
        , $(normal [| \s v -> length s > 0 && length s == length v && n > length s |]  ) $
            $(update [p| x:xs |] [p| x:xs |] [d| x = Replace; xs = lensTake (n-1) |])
        -- condition c2
        , $(normal [| \s v -> length s >= 0 && length v == 0 && n == 0 |]  ) $
            $(update [p| [] |] [p| _ |] [d| |])
        -- condition c2
        , $(normal [| \s v -> length s > 0 && n == length v && length v > 0 |]  ) $
            $(update [p| x:xs |] [p| x:xs |] [d| x = Replace; xs = lensTake (n-1) |])
        ]

-- put semantics: replace the last n elements of a source list
-- well-behaved state consistency: length s <= n + length v
-- well-behaved state consistency (precise): length s = n + length v || (length s <= n && length v = 0)
lensDrop :: (Typeable a, Defaultable a) => Int -> BiGUL [a] [a]
lensDrop n =
  Case  [ $(adaptive [| \s v -> not (length s == n + length v || (length s <= n && length v == 0) ) |] ) $
            (\s v ->  let ls = length s
                          lv = length v
                      in  if lv > ls - n
                            then  if ls >= n -- should add missing elements to the source
                                    then
                                      -- source is larger enough, just keep the first n elements and replace the remainings)
                                      take n s ++ v
                                    else
                                      -- source is not larger enough. should fill the source into a proper length according to n. then concate the view to the source.
                                      (replicate (n - ls) (defaultVal . show . typeOf $ s )) ++ s ++ v
                            else  if ls - n >= 0
                                    then
                                      -- source is large enough. should preserve the first n elements. then concate view to the source
                                      take n s ++ v
                                    else
                                      -- source is not large enough. enlarge the source. then concate the view.
                                      (replicate (n - ls) (defaultVal . show . typeOf $ s )) ++ s ++ v
            )
        , $(normal [| \s v -> n > 0 && (length s == n + length v || (length s <= n && not (null v))) |] )
            -- skip the first n elements
            $(update [p| xs |] [p| _:xs |] [d| xs = lensDrop (n-1) |])
        , $(normal [| \s v -> n == 0 && (length s == n + length v || (length s <= n && not (null v) )) |] )
            $(update [p| xs |] [p| xs |] [d| xs = replaceByPosition |])
            -- caution. pattern overlaps. this incomplete condition should be put last
        , $(normal [| \s v -> null v |] )
            $(update [p| [] |] [p| _ |] [d|  |])
        ]


-- takeWhile :: (a -> Bool) -> [a] -> [a]

-- dropWhile :: (a -> Bool) -> [a] -> [a]

-- put semantics: replacet he maximum value with a new one
-- pre condition: in general, the view should be no less than the second large element in the source
-- however, we enforce the view should be larger than the second largest element. The following situation is prohibited:
-- put [4,5,6,1] 5 -> [4,5,5,1]. the first 5 is choosed when performing get. though the result is the same, the branch is different.
lensMaximum :: (Ord a) => BiGUL [a] a
lensMaximum =
    Case  [ $(normal [| \s v -> v <= secondMax s |] )
              (Fail "the view should be greater than the second smallest element in the list")
          , $(normal [| \s v -> head s == maximum s |] ) $
               $(update [p| v |] [p| v:_ |] [d| v = Replace |])
          -- overlapped pattern. be careful.
          , $(normalS [p| _ |] ) $
              $(update [p| v |] [p| _:v |] [d| v = lensMaximum |])
          ]



-- minimum

-- repeat :: a -> [a]

-- replicate :: Int -> a -> [a]

-- cycle :: [a] -> [a]

-- reverse :: [a] -> [a]


-- inits :: [a] -> [[a]]

-- tails :: [a] -> [[a]]


---- trivial well-behaved wrapper
emb :: Eq v => (s -> v) -> (s -> v -> s) -> BiGUL s v
emb g p = Case
  [ $(normal [| \x y -> g x == y |])$
      $(rearrV [| \x -> ((), x) |])$
        Dep Skip (\x () -> g x)
  , $(adaptive [| \_ _ -> True |])
      p
  ]

-- for now we can only use emb or Nat datatype.
lengthEmb :: (Typeable a, Defaultable a) => BiGUL [a] Int
lengthEmb = emb (length)
  (\s v ->
    let ls = length s
    in  if ls == v
          then s
          else  if ls > v
                  then drop (ls - v) s
                  --else  if ls == 0
                  --        then error "a proper source cannot be generated: the original source is empty and the type is unknown"
                          else s ++ (replicate (v - ls) (defaultVal  (show (typeOf s)) )))



--haha :: BiGUL [a] Nat
--haha = Case [ $(normal [| \s v -> length s == 0 && v == Zero |] ) $
--                $(rearrV [| \Zero -> () |]) $
--                  $(update [p| () |] [p| _ |] [d| |])
--            , $(normalSV [p| _:_ |] [p| Succ _ |] ) $
--              --  $(rearrV [| \(x:xs) -> ((),xs) |])
--                  $(update [p| Succ xs |] [p| _:xs |] [d| xs = haha |])
--            ]


--nat2Int :: BiGUL Int Nat
--nat2Int =  Case [ $(normalV [p| Zero |] ) $
--                  --  $(rearrS [| \s -> 0 |]) $
--                      $(rearrV [| \Zero -> () |]) $
--                        $(update [p| () |] [p| _ |] [d|  |])
--                , $(normalSV [| \s -> 0 < s  |] [p| Succ _ |] ) $
--                  --  $(rearrS [| \s -> s |]) $
--                    --  $(rearrV [| \(Succ nat) -> nat |]) $
--                        $(update [p| Succ nat |] [p| nat |] [d| nat = nat2Int |])
--                ]

isEqNatInt :: Int -> Nat -> Bool
isEqNatInt 0 Zero       = True
isEqNatInt 0 (Succ _)   = False
isEqNatInt n (Succ nat) = isEqNatInt (n-1) nat
isEqNatInt _ Zero       = False



-- generate default value for some common datatypes
class Defaultable a where
  defaultVal :: String -> a

instance Defaultable Int where
  defaultVal _ = 0

instance Defaultable Integer where
  defaultVal _ = 0

instance Defaultable String where
  defaultVal _ = ""

instance Defaultable Bool where
  defaultVal _ = False

instance Defaultable Char where
  defaultVal _ = '\0'

instance Defaultable Float where
  defaultVal _ = 0


data Nat = Zero | Succ Nat deriving (Show, Eq)

deriveBiGULGeneric ''Nat



