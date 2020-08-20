DOC=cost-model-notes

PDF=${DOC}.pdf

FIGS=./figures

SRC = ${DOC}.tex


LATEX = pdflatex -halt-on-error -shell-escape

.PHONEY: all pdf figs again clean 

#----------------------------------------------------------------

all: pdf

pdf: ${PDF}

${DOC}.pdf: ${SRC}
	-rm -f ${DOC}.bbl ${DOC}.aux
	${LATEX}  ${DOC}
	${LATEX}  ${DOC}
	${LATEX}  ${DOC}

figs:
	cd ${FIGS} && ${MAKE}

#----------------------------------------------------------------
again: 
	touch ${DOC}.tex && ${MAKE}

clean:
	rm -f *.aux *.log *.cov *.par *.bbl *.fls *.blg *.xml *.bcf *.dvi *~
	cd ${FIGS} && ${MAKE} clean

clean2: clean
	rm -f ${DOC}.pdf

v: ${PDF}
	acroread ${PDF} 2>/dev/null &

