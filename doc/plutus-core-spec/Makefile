DOC=plutus-core-specification

PDF=${DOC}.pdf
BIB=${DOC}.bib

FIGS=./figures

SRC = *.tex cardano/*.tex ${BIB} # ${FIGS}/*.tex 


LATEX = pdflatex -halt-on-error -shell-escape # To get pstricks to work with PDF
BIBTEX = bibtex
MAKEINDEX = makeindex

.PHONEY: all pdf figs again clean 

#----------------------------------------------------------------

all: pdf

pdf: ${PDF}

${DOC}.pdf: ${SRC} ${BIB}
	-rm -f ${DOC}.bbl ${DOC}.aux ${DOC}.nls ${DOC}.nlo
	${LATEX}  ${DOC}
	${BIBTEX} ${DOC}
	${LATEX}  ${DOC}   # to make sure the (cross)references are correct
	${MAKEINDEX} ${DOC}.nlo -s nomencl.ist -o ${DOC}.nls
        # ^ Putting this later seems to get page references out of sync.
	${LATEX}  ${DOC}
	${LATEX}  ${DOC}
	${LATEX}  ${DOC}

figs:
	cd ${FIGS} && ${MAKE}

#----------------------------------------------------------------
again: 
	touch ${DOC}.tex && ${MAKE}

clean:
	rm -f *.aux *.log *.cov *.par *.bbl *.fls *.blg *.out *.xml *.bcf *.dvi *.toc *.tdo *.nls *.nlo *.ilg *~

clean2: clean
	rm -f ${DOC}.pdf

v: ${PDF}
	${PDFVIEWER} ${PDF} 2>/dev/null &

