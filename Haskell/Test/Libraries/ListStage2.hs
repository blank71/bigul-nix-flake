{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

import ListStage1

import GHC.Generics
import Generics.BiGUL.AST
import Generics.BiGUL.TH
import Generics.BiGUL.Interpreter

import Language.Haskell.TH as TH hiding (Name)


import Data.Typeable

data Nat = Zero | Succ Nat deriving (Show, Eq)

deriveBiGULGeneric ''Nat

--import Data.Set
--import Control.Monad.Except

bHead  = get bHead_
bpHead = put bHead_

blast  = get bLast_
bpLast = put bLast_

--btailSafe  = get bTailSafe_
--bptailSafe = put bTailSafe_

btail  = get bTailStrict_
bptail = put bTailStrict_

binit  = get binitStrict_
bpinit = put binitStrict_

bnull  = get bnull_
bpnull = put bnull_

-- put semantics: replace the first element in list with the provided one
-- work only with non-empty list
bHead_ :: BiGUL [a] a
bHead_ = $(update [p| x |] [p| x:_ |]  [d| x = Replace |])

-- work only with non-empty list
bLast_ :: BiGUL [a] a
bLast_ = Case [$(normalS [p| [_] |])
                  $(update [p| x |] [p| x:[] |] [d| x = Replace  |])
              ,$(normalS [p| _:_ |])
                  $(update [p| x |] [p| _:x |] [d| x = bLast_ |])  ]



--bTailSafe_ :: BiGUL [a] [a]
--bTailSafe_ = Case [ $(adaptive [|\s v -> length s /= 1 + length v |])
--                        (\_ v -> replicate (1 + length v) undefined)
--                  , $(normalS [p| _:_ |])
--                       $(update [p| x |] [p| _:x |] [d| x = replaceByPosition |])
--                 ]

-- work only with non-empty list
-- giving a list of length n, replace its tail list with a new list of length (n-1)
bTailStrict_ :: BiGUL [a] [a]
bTailStrict_ = Case [ $(adaptive [|\s v -> length s /= 1 + length v |])
                        (\_ _ -> error "length mismatch")
                    , $(normalS [p| _:_ |])
                          $(update [p| x |] [p| _:x |] [d| x = replaceByPosition |])
                    ]

-- to do.
binitStrict_ :: BiGUL [a] [a]
binitStrict_ = Case [ $(adaptive [|\s v -> length s /= 1 + length v |])
                        (\_ _ -> error "length mismatch")
                    , $(normalSV [p| _:_ |] [p| _:_ |] )
                          $(update [p| x:xs |] [p| x:xs |] [d| x = Replace; xs = binitStrict_ |])
                    , $(normalSV [p| [_] |] [p| [] |] )
                          $(update [p| [] |] [p| [_] |] [d| |])
                    ]

bnull_ :: BiGUL [a] Bool
bnull_ = Case [$(normalSV [p| [] |] [p| True |]  ) $
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

blengthStrict_ :: BiGUL [a] Int
blengthStrict_ = Case [ $(normal [| \s v -> length s == v |] ) $
                          $(rearrV [| \v -> () |])
                            $(update [p| () |] [p| _ |] [d|  |])
                      , $(adaptive  [|\ _ _ -> True|])  (\_ _ -> error "length mismatch")]

-- Dep     :: (Eq v') => BiGUL s v -> (s -> v -> v') -> BiGUL s (v, v')

--hehe :: BiGUL [Int] Int
--hehe = Case [ $(normal [| \s v -> length s == v |] ) $
--                  Dep Replace (\_ v -> v+1)
--                          $(rearrV [| \v -> () |])
--                            $(update [p| () |] [p| _ |] [d|  |])
--                      , $(adaptive  [|\ _ _ -> True|])  (\_ _ -> error "length mismatch")]

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
