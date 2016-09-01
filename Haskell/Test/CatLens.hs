{-# LANGUAGE TemplateHaskell, TypeFamilies, TupleSections #-}

module CatLens where

import GHC.Generics

import Generics.BiGUL
import Generics.BiGUL.TH
import Generics.BiGUL.Lib
import Generics.BiGUL.Lib.List
import Generics.BiGUL.Interpreter


type Picture = String
type Name    = String

data FS = Directory Name [FS]
        | File Name Picture
        deriving (Show, Eq)

deriveBiGULGeneric ''FS

type Tag = String
type Web = [(Picture, [Tag])]

pushdown :: BiGUL FS FS
pushdown = Case
  [ $(normalSV [p| Directory _ (Directory _ [] : _) |] [p| Directory _ _ |]
               [p| Directory _ (Directory _ [] : _) |])
    ==> $(update [p| Directory dirName (Directory _ [] : fs) |] [p| Directory dirName fs |]
                 [d| dirName = Replace
                     fs      = align (const True) (\_ _ -> True) Replace (const (Directory "???" [])) (const Nothing) |])
  , $(normalSV [p| Directory _ (Directory _ (_:_) : _) |] [p| Directory _ (_:_) |]
               [p| Directory _ (Directory _ (_:_) : _) |])
    ==> $(rearrS [| \(Directory dirName (Directory dirName' (x:xs) : fs)) ->
                      (x, Directory dirName (Directory dirName' xs : fs)) |])$
          $(rearrV [| \(Directory dirName (x:xs)) -> (x, Directory dirName xs) |])$
            Replace `Prod` pushdown
  ]

catLensL :: BiGUL FS [Picture]
catLensL = Case
  [ $(normalSV [p| Directory _ [] |] [p| [] |] [p| Directory _ [] |])
    ==> $(update [p| _ |] [p| [] |] [d| |])
  , $(normalSV [p| Directory _ (File _ _ : _) |] [p| _:_ |] [p| Directory _ (File _ _ : _) |])
    ==> $(rearrS [| \(Directory dirName (File _ pic : fs)) -> (pic, Directory dirName fs) |])$
          $(rearrV [| \(pic:pics) -> (pic, pics) |])$
            Replace `Prod` catLensL
  , $(normalSV [p| Directory _ (Directory _ _ : _) |] [p| _:_ |] [p| Directory _ (Directory _ _ : _) |])
    ==> pushdown `Compose` catLensL
  , $(adaptiveSV [p| Directory _ [] |] [p| _:_ |])
    ==> \(Directory dirName _) pics -> Directory dirName (replicate (length pics) (File "???" ""))
  ]

catLensR :: BiGUL Web [Picture]
catLensR = align (const True) (\_ _ -> True) $(update [p| (pic, _) |] [p| pic |] [d| pic = Replace |]) (,[]) (const Nothing)

putR :: FS -> Web -> Maybe Web
putR fs web = put catLensR web =<< get catLensL fs

putL :: FS -> Web -> Maybe FS
putL fs web = put catLensL fs =<< get catLensR web


--------
-- Martin’s test cases

fs0 :: FS
fs0 = Directory "root"
        [ Directory "Jan"
            [ File "palindrome.jpg"
                   "cat0"
            , File "gamer.jpg"
                   "cat1" ]
        , Directory "May"
            [ File "froghead.jpg"
                   "cat2" ] ]

web0 :: Web
web0 = [ ("cat0", ["costume", "food"])
       , ("cat1", ["costume"        ])
       , ("cat2", ["costume"        ]) ]

fs1 :: FS
fs1 = Directory "root"
        [ Directory "Jan"
            [ File "palindrome.jpg"
                   "cat0"
            , File "gamer.jpg"
                   "cat1" ]
        , Directory "May"
            [ File "froghead.jpg"
                   "cat2" ]
        , File "???"
               "cat3" ]

web1 :: Web
web1 = [ ("cat0", ["costume", "food"])
       , ("cat1", ["costume"        ])
       , ("cat2", ["costume"        ])
       , ("cat3", ["onlyface"       ]) ]

goal1 :: Bool
goal1 = putL fs0 web1 == Just fs1

fs2 :: FS
fs2 = Directory "root"
        [ Directory "Jan"
            [ File "palindrome.jpg"
                   "cat0"
            , File "gamer.jpg"
                   "cat1" ]
        , Directory "May"
            [ File "froghead.jpg"
                   "cat2" ]
        , File "burrito.jpg"
               "cat3" ]

web2 :: Web
web2 = web1

goal2 :: Bool
goal2 = putR fs2 web1 == Just web2

fs3 :: FS
fs3 = fs2

web3 :: Web
web3 = [ ("cat0", ["costume", "food" ])
       , ("cat1", ["costume"         ])
       , ("cat2", ["costume"         ])
       , ("cat3", ["food", "onlyface"]) ]

goal3 :: Bool
goal3 = putL fs2 web3 == Just fs3

fs4 :: FS
fs4 = Directory "root"
        [ Directory "Jan"
            [ File "palindrome.jpg"
                   "cat0"
            , File "gamer.jpg"
                   "cat1" ]
        , Directory "May"
            [ File "froghead.jpg"
                   "cat2" ]
        , File "burrito.jpg"
               "cat3"
        , File "whiteperson.jpg"
               "cat4" ]

web4 :: Web
web4 = [ ("cat0", ["costume", "food" ])
       , ("cat1", ["costume"         ])
       , ("cat2", ["costume"         ])
       , ("cat3", ["food", "onlyface"])
       , ("cat4", [                  ]) ]

goal4 :: Bool
goal4 = putR fs4 web3 == Just web4

fs5 :: FS
fs5 = Directory "root"
        [ Directory "2010"
            [ Directory "Jan"
                [ File "palindrome.jpg"
                       "cat0"
                , File "gamer.jpg"
                       "cat1" ]
            , Directory "May"
                [ File "froghead.jpg"
                       "cat2" ] ]
        , Directory "2011"
            [ File "burrito.jpg"
                   "cat3"
            , File "whiteperson.jpg"
                   "cat4" ] ]

web5 :: Web
web5 = web4

goal5 :: Bool
goal5 = putR fs5 web4 == Just web5

goals :: Bool
goals = goal1 && goal2 && goal3 && goal4 && goal5
