all: 
	@rm -f paper.dvi
	@rm -f paper.aux
	latex paper
	bibtex paper
	latex paper
	latex paper
	pdflatex paper


%.dvi : %.tex
	latex $*.tex

%.ps : %.dvi
	dvips -t letter -o $*.ps $*.dvi

%.pdf : %.ps
	ps2pdf $*.ps $*.pdf

