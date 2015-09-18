all:
	cabal configure --prefix=${HOME} --user
	cabal build
	cabal install

bigul:
	ghci -isrc:Test/test/bookmark  Test/Test.hs

dtd:
	ghci -isrc Test/TestGenDTD.hs

rxml:
	ghci -isrc:Test/test/bookstore Test/ReadXML.hs

type:
	ghci -isrc Test/TestType.hs

subtype:
	ghci -isrc -XGADTs -XViewPatterns -XImpredicativeTypes -XTypeFamilies -XTypeOperators -XFlexibleContexts -XRank2Types -XTemplateHaskell -XFlexibleInstances -XUndecidableInstances -XScopedTypeVariables Test/TestSubTyping.hs

tran:
	ghci -isrc Test/TestTranslation.hs


