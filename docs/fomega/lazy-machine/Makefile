DOC=lazy-plutus-core
PDF=${DOC}.pdf
BIB=${DOC}.bib

SRC = ${DOC}.tex ckmachine.tex cekmachine.tex lmachine.tex ${BIB}


FIGS=./figs

LATEX = pdflatex -halt-on-error -shell-escape # To get pstricks to work with PDF
BIBTEX = bibtex

.PHONEY: all pdf v clean # figs pngs

#----------------------------------------------------------------

all: pdf

pdf: ${PDF}

${DOC}.pdf: ${SRC} ${BIB}
	${LATEX}  ${DOC}
	${BIBTEX} ${DOC}
	${LATEX}  ${DOC}   # to make sure the (cross)references are correct
	${LATEX}  ${DOC}

figs:
	cd ${FIGS} && ${MAKE}

pngs:
	cd ${FIGS} && ${MAKE} pngs
#----------------------------------------------------------------

v: ${DOC}.pdf
	acroread ${DOC}.pdf

clean:
	rm -f *.aux *.log *.cov *.par *.bbl *.fls *.blg *.xml *.bcf *~
#	cd ${FIGS} && ${MAKE} clean

clean2:
	${MAKE} clean && rm -rf ${PDF}
