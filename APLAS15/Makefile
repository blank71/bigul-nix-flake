LaTeX = pdflatex
# lhs2TeX = /Users/hu/Library/Haskell/bin/lhs2TeX
lhs2TeX = lhs2TeX

APLAS15: APLAS15-processed.tex introduction.tex
#	$(LaTeX) -jobname APLAS15 APLAS15-processed.tex
	$(LaTeX) APLAS15-processed.tex
	bibtex APLAS15-processed
	$(LaTeX) APLAS15-processed.tex
	cp APLAS15-processed.pdf APLAS15.pdf

APLAS15-processed.tex: APLAS15.tex APLAS15.def introduction.tex
	$(lhs2TeX) --agda --hyp-def=APLAS15.def APLAS15.tex -o APLAS15-processed.tex

APLAS15.def: APLAS15.tex
	$(lhs2TeX) --agda --collect-def APLAS15.tex > APLAS15.def
