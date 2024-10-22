DOC=cost-model-overview

PDF=${DOC}.pdf
BIB=${DOC}.bib

SRC = ${DOC}.tex 

LATEX = pdflatex -halt-on-error -shell-escape

.PHONEY: all pdf again clean 

#----------------------------------------------------------------

all: pdf

pdf: ${PDF}

${DOC}.pdf: ${SRC} 
	-rm -f ${DOC}.bbl ${DOC}.aux ${DOC}.nls ${DOC}.nlo
	${LATEX}  ${DOC}
	${LATEX}  ${DOC}   # to make sure the (cross)references are correct
	${LATEX}  ${DOC}

#----------------------------------------------------------------
again: 
	touch ${DOC}.tex && ${MAKE}

clean:
	rm -f *.aux *.log *.cov *.par *.bbl *.fls *.blg *.out *.xml *.bcf *.dvi *.toc *.tdo *.nls *.nlo *.ilg *~

clean2: clean
	rm -f ${DOC}.pdf

v: ${PDF}
	${PDFVIEWER} ${PDF} 2>/dev/null &
