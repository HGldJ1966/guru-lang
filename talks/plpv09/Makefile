all: 
	@rm -f talk.aux
	pdflatex talk.tex

%.dvi : %.tex
	latex $*.tex

%.ps : %.dvi
	dvips -t letter -o $*.ps $*.dvi


%.pdf : %.tex
	pdflatex $*.tex
