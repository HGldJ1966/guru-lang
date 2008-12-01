submitted: plpv03-stump.pdf plpv03-stump.ps

plpv03-stump.pdf: 
	@rm -f plpv03-stump.dvi
	@rm -f plpv03-stump.aux
	latex plpv03-stump
#	bibtex plpv03-stump
#	latex plpv03-stump
	latex plpv03-stump
	pdflatex plpv03-stump


%.dvi : %.tex
	latex $*.tex

%.ps : %.dvi
	dvips -t letter -o $*.ps $*.dvi

