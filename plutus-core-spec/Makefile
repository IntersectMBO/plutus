DOC=plutus-core-specification

PDF=${DOC}.pdf
BIB=${DOC}.bib

FIGS=./figures

SRC = ${DOC}.tex ${BIB} ${FIGS}/*.tex 


LATEX = pdflatex -halt-on-error -shell-escape # To get pstricks to work with PDF
BIBTEX = bibtex

.PHONEY: all pdf figs again clean 

#----------------------------------------------------------------

all: pdf

pdf: ${PDF}

${DOC}.pdf: ${SRC}
	-rm -f ${DOC}.bbl ${DOC}.aux
	${LATEX}  ${DOC}
	${BIBTEX} ${DOC}
	${LATEX}  ${DOC}   # to make sure the (cross)references are correct
	${LATEX}  ${DOC}
	${LATEX}  ${DOC}

figs:
	cd ${FIGS} && ${MAKE}

#----------------------------------------------------------------
again: 
	touch ${DOC}.tex && ${MAKE}

clean:
	rm -f *.aux *.log *.cov *.par *.bbl *.fls *.blg *.xml *.bcf *.dvi *.out *~
	cd ${FIGS} && ${MAKE} clean

clean2: clean
	rm -f ${DOC}.pdf

v: ${PDF}
	acroread ${PDF} 2>/dev/null &

