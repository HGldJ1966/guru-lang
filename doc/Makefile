all: 
	@rm -f book.aux
	@rm -f book.dvi
	$(MAKE) book.dvi
#	bibtex book
#	@rm -f book.dvi
#	$(MAKE) book.dvi
#	@rm -f book.dvi
	$(MAKE) book.pdf


%.dvi : %.tex
	latex $*.tex

%.ps : %.dvi
	dvips -t letter -o $*.ps $*.dvi

%.pdf : %.tex
	pdflatex $*.tex
