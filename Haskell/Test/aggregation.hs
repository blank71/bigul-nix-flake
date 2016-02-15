{-# LANGUAGE TypeOperators, TypeFamilies, FlexibleContexts, DeriveGeneric, ViewPatterns  #-}

import GHC.Generics
import Generics.BiGUL
import Generics.BiGUL.AST
import Language.Haskell.TH as TH hiding (Name)
import Generics.BiGUL.TH
import Data.List
import Data.Maybe
import Control.Monad.Except



data Nat = Z | S Nat deriving (Show,Eq)
deriveBiGULGeneric ''Nat

lessOrEqual Z _ = True
lessOrEqual (S a) (S b) = lessOrEqual a b
lessOrEqual _ _ = False

greatOrEqual _ Z = True
greatOrEqual (S a) (S b) = greatOrEqual a b
greatOrEqual _ _ = False

int2Nat :: Int -> Nat
int2Nat 0 = Z
int2Nat n = S (int2Nat (n-1))

nat2Int :: Nat -> Int
nat2Int Z = 0
nat2Int (S n) = 1 + nat2Int n

sub :: BiGUL (Nat,Nat) Nat
sub = Case [ $(normal [| \(ls,_) v -> not (lessOrEqual ls v)|]) $
              Fail "(ls,_)  v : ls must be lessOrEqual than v",
             $(normalS [p| (Z,_) |] ) $
              $(rearrV [| \v -> (Z,v) |]) Replace,
             $(normalSV [p| (S _ , _) |] [p| S _ |]) $
              $(rearrV [| \(S v) -> v |])
               ($(rearrS [| \(S ls, rs) -> (ls , rs) |]) sub)
           ]

putSumVZ :: BiGUL [Nat] Nat
putSumVZ = Case [ $(normalSV [p| [] |] [p| Z |]) $
                   $(rearrV [| \Z -> [] |]) Replace,
                  $(normalV [p| Z |]) $
                   $(rearrV [| \Z -> (Z, Z) |]) $
                    ($(rearrS [| \(x:xs) -> (x,xs) |]) (Prod Replace putSumVZ)),
                  $(normalV [p| _ |]) $
                    Fail "View Nat is not Z"
                ]


putSum :: BiGUL [Nat] Nat
putSum =  Case [ $(normalV [p| Z |]) $
                  putSumVZ,
                 $(adaptiveS [p| [] |]) $
                  \_ v -> [v],
                 $(normalS [p| Z:_ |]) $
                  $(rearrS [| \(_:s) -> s |]) putSum,
                 $(normalSV [p| S _:_ |] [p| S _ |]) $
                  $(rearrV [| \(S v) -> v|])
                    ($(rearrS [| \((S x):xs) -> x:xs|]) putSum),
                 $(normalSV [p| _ |] [p| _ |]) $
                  Fail "putSum error"
               ]




lrotateHelper :: Eq a =>  BiGUL [a] [a]
lrotateHelper = $(update    [p| x:xs |]
                            [p| x:xs |]
                            [d| x = Replace ; xs = lrotate|])


lrotate :: Eq a =>  BiGUL [a] [a]
lrotate = Case [ $(normalV [p| [] |]) Replace,
                 $(normalV [p| [_] |]) Replace,
                 $(adaptiveS [p| [] |]) $
                   \_ _ -> [undefined] ,
                 $(normalV [p| _ |]) $
                    ((flip Compose)
                        ($(rearrV [| \(a:b:xs) -> b:a:xs |]) Replace)
                        lrotateHelper)
               ]

lreverse :: Eq a => BiGUL [a] [a]
lreverse = Case [ $(normalV [p| [] |]) Replace,
                  $(adaptiveS [p| [] |]) $
                   \_ _ -> [undefined] ,
                  $(normalV [p| _ |]) $
                    ((flip Compose)
                 ($(update  [p| x:xs |]
                            [p| x:xs |]
                            [d| x = Replace ; xs = lreverse|]))
                   lrotate)
                ]

putSum2 :: BiGUL [Nat] Nat
putSum2 = ((flip Compose) putSum
             lreverse)

