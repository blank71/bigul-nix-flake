bigul:
	ghci -isrc `cat ghc-options` Test/Test.hs

dtd:
	ghci -isrc Test/TestGenDTD.hs

rxml:
	ghci -isrc:Test/test/bookstore Test/ReadXML.hs

type:
	ghci -isrc Test/TestType.hs

subtype:
	ghci -isrc -XGADTs -XViewPatterns -XImpredicativeTypes -XTypeFamilies -XTypeOperators -XFlexibleContexts -XRank2Types -XTemplateHaskell -XFlexibleInstances -XUndecidableInstances -XScopedTypeVariables Test/TestSubTyping.hs
