LaTeX = pdflatex
lhs2TeX =lhs2TeX

FILE=icfp16
REFS=references.bib

.PHONY: paper clean

paper : $(FILE).bbl $(FILE).tex
	$(LaTeX) $(FILE).tex

%.tex : %.lhs
	lhs2TeX --poly $< > $@

$(FILE).aux : $(FILE).tex
	$(LaTeX) $(FILE).tex

$(FILE).bbl : $(FILE).aux $(REFS)
	bibtex $<

clean :
	-rm *.aux *.bbl *.blg *.log *.ptb
