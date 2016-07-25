{-# LANGUAGE FlexibleContexts, TemplateHaskell, TypeFamilies #-}
import Generics.BiGUL
import Generics.BiGUL.Interpreter
import Generics.BiGUL.TH
import Generics.BiGUL.Lib

-- hello: _ <-> Hello!
hello :: Show a => BiGUL a String
hello = Skip (\_ -> "Hello!")
