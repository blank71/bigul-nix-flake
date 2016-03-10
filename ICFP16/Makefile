LaTeX = pdflatex
lhs2TeX =lhs2TeX

FILE=icfp16
REFS=references.bib
LITERATE=lhs2tex.tex \
  basicput.tex \
  positional.tex \
  keybased.tex

.PHONY: paper clean

paper : $(FILE).bbl $(LITERATE)
	$(LaTeX) $(FILE).tex

$(FILE).aux : $(FILE).tex $(LITERATE)
	$(LaTeX) $(FILE).tex

$(FILE).bbl : $(FILE).aux $(REFS)
	bibtex $<

clean :
	-rm *.aux *.bbl *.blg *.log $(LITERATE)

# Literate Haskell

LHSCMD=lhs2TeX --poly $< > $@

%.tex : %.lhs
	$(LHSCMD)
