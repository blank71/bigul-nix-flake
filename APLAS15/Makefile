LaTeX = pdflatex
lhs2TeX = /Users/joshko/Library/Haskell/bin/lhs2TeX

APLAS15: APLAS15-processed.tex
	$(LaTeX) -jobname APLAS15 APLAS15-processed.tex

APLAS15-processed.tex: APLAS15.tex APLAS15.def
	$(lhs2TeX) --agda --hyp-def=APLAS15.def APLAS15.tex -o APLAS15-processed.tex

APLAS15.def: APLAS15.tex
	$(lhs2TeX) --agda --collect-def APLAS15.tex > APLAS15.def
