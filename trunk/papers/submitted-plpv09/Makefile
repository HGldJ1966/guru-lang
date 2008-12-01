submitted: paper.pdf paper.ps
	mv paper.pdf plpv03-stump.pdf
	mv paper.ps plpv03-stump.ps

paper.pdf: 
	@rm -f paper.dvi
	@rm -f paper.aux
	latex paper
#	bibtex paper
#	latex paper
	latex paper
	pdflatex paper


%.dvi : %.tex
	latex $*.tex

%.ps : %.dvi
	dvips -t letter -o $*.ps $*.dvi

