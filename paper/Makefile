coqsem.pdf: coqsem.tex
	pdflatex --halt-on-error coqsem
	bibtex coqsem
	pdflatex --halt-on-error coqsem
	pdflatex --halt-on-error coqsem

clean:
	@ rm -f coqsem.aux coqsem.out coqsem.log coqsem.pdf coqsem.bbl coqsem.blg
