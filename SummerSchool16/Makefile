TEX=platex
BIB=bibtex
DVIPS=`if which dvipsk > /dev/null; then echo dvipsk; else echo dvips; fi` -Ppdf -t letter

DVIPDF=dvipdfmx
PS_PDF=ps2pdf14
RM=rm -f
MAIN=paper

BIB_FILE=references.bib

FILES=$(MAIN).tex PBasic.lhs PList.lhs PSet.lhs Principle.lhs Implementation.lhs Delta.lhs BiYacc.lhs

TEX_FILE=$(MAIN).tex
DVI_FILE=$(MAIN).dvi
PS_FILE=$(MAIN).ps
PDF_FILE=$(MAIN).pdf
AUX_FILE=$(MAIN).aux
BBL_FILE=$(MAIN).bbl

.phony : clean clean_all dvi ps pdf all

default : pdf

clean :
	$(RM) *.aux *.blg *.bbl *.dvi *.log *.toc *.pbm *~ $(MAIN).p* PBasic.tex PList.tex PSet.tex Principle.tex Implementation.tex Delta.tex BiYacc.tex

all_clean : clean
	$(RM) $(PS_FILE) $(PDF_FILE)

dvi : $(DVI_FILE)

ps : $(PS_FILE)

pdf : $(PDF_FILE)

all : $(DVI_FILE) $(PS_FILE) $(PDF_FILE)

$(AUX_FILE) : $(FILES)
	$(TEX) $(TEX_FILE)
	$(RM) $(DVI_FILE)

$(BBL_FILE) : $(AUX_FILE) $(BIB_FILE)
	$(BIB) $(MAIN)

$(DVI_FILE) : $(FILES) $(BBL_FILE)
	$(TEX) $(TEX_FILE)
	$(TEX) $(TEX_FILE)

$(PS_FILE) : $(DVI_FILE)
	$(DVIPS) $(DVI_FILE)

#$(PDF_FILE) : $(PS_FILE)
#	$(PS_PDF) $(PS_FILE)

#$(PDF_FILE) : $(DVI_FILE)
#	$(DVIPDF) $(DVI_FILE)

$(PDF_FILE) : $(FILES)
	pdflatex $(TEX_FILE)
	$(BIB) $(MAIN)
	pdflatex $(TEX_FILE)
	pdflatex $(TEX_FILE)

$(MAIN).tex: lhs2TeX-polycode.sty lhs2TeX-macros.lhs PBasic.tex PList.tex PSet.tex Principle.tex Implementation.tex Delta.tex BiYacc.tex

lhs2TeX-polycode.sty: lhs2TeX-polycode.lhs
	lhs2TeX --output=$@ $<

%.tex: %.lhs lhs2TeX-macros.lhs
	lhs2TeX --output=$@ $<

inputtree.pdf: inputtree.dot
	dot -Tpdf -o $@ $<

SUBMITDIR=_submit
submit: $(MAIN).tex
	rm -rf $(SUBMITDIR)
	mkdir $(SUBMITDIR)
	cat $(MAIN).tex | sed -e 's/.*\\input{\([^}].*\)}.*/cat \1.tex/e' > $(SUBMITDIR)/submit.tex
	cp references.bib lhs2TeX-polycode.sty llncs.cls splncs03.bst inputtree.pdf lazylist.sty polytable.sty remreset.sty $(SUBMITDIR)
	cd $(SUBMITDIR); pdflatex submit; bibtex submit; pdflatex submit; pdflatex submit
	cd $(SUBMITDIR); rm submit.bbl submit.aux submit.blg submit.ptb submit.log
	rm -rf submit.pdf submit.zip
	mv $(SUBMITDIR)/submit.pdf ./; cd $(SUBMITDIR); zip ../submit.zip *
