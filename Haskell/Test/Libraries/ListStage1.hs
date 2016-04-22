{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module ListStage1 where

import Generics.BiGUL.AST
import Generics.BiGUL.Interpreter
import Language.Haskell.TH as TH hiding (Name)
import Generics.BiGUL.TH


replaceByPosition :: BiGUL [a] [a]
replaceByPosition = Case  [ $(normalSV [p| [] |] [p| [] |] )
                              $(update [p| [] |] [p| [] |] [d| |])
                          , $(normalSV [p| _:_ |] [p| _:_ |] )
                              $(update [p| x:xs |] [p| x:xs |] [d| x = Replace; xs = replaceByPosition |])
                     ]

