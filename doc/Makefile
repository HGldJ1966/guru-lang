all: 
	@rm -f book.aux
	@rm -f book.out
	latex book.tex
#	bibtex book
#	latex book.tex
#	latex book.tex
	pdflatex book.tex

bib:
	bibtex book
	latex book.tex
	pdflatex book.tex