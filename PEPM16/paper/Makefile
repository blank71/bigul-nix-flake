LaTeX = pdflatex
lhs2TeX =lhs2TeX

PEPM16: PEPM16-processed.tex
	$(LaTeX) -jobname PEPM16 PEPM16-processed.tex

PEPM16-processed.tex: PEPM16.tex PEPM16.def
	$(lhs2TeX) --agda --hyp-def=PEPM16.def PEPM16.tex -o PEPM16-processed.tex

PEPM16.def: PEPM16.tex
	$(lhs2TeX) --agda --collect-def PEPM16.tex > PEPM16.def

