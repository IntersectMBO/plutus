DOC=utxoma

PDF=${DOC}.pdf 
BIB=${DOC}.bib

FIGS=./figures

SRC = *.tex ${BIB}


LATEX = pdflatex -halt-on-error -shell-escape # To get pstricks to work with PDF
BIBTEX = bibtex

.PHONEY: all pdf figs again clean 

#----------------------------------------------------------------

all: pdf

pdf: ${PDF}

${DOC}.pdf: ${SRC}
	rm -f ${DOC}.bbl
	${LATEX} ${DOC}
	${BIBTEX} ${DOC}
	${LATEX}  ${DOC}   # to make sure the (cross)references are correct
	${LATEX}  ${DOC}

figs:
#	cd ${FIGS} && ${MAKE}

#----------------------------------------------------------------
again: 
	touch ${DOC}.tex && ${MAKE}

clean1:
	rm -f *.aux *.log *.cov *.par *.bbl *.fls *.blg *.xml *.bcf *.dvi *.out *~
#	cd ${FIGS} && ${MAKE} clean

clean: clean1
	rm -f ${DOC}.pdf

v: ${PDF}
	acroread 2>/dev/null ${PDF}

