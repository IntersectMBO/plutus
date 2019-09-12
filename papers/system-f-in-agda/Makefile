DOC=paper
BIBFILE =bibliography
PDF=${DOC}.pdf
BIB=${BIBFILE}.bib

LAGDA = ${DOC}.lagda
SRC = ${DOC}.tex ${BIB} 

AGDA = agda --latex --latex-dir .
LATEX = pdflatex -halt-on-error -shell-escape # To get pstricks to work with PDF
BIBTEX = bibtex

.PHONEY: all pdf figs again clean 

#----------------------------------------------------------------

all: pdf

pdf: ${PDF}

${DOC}.pdf: ${LAGDA}
	${AGDA}   ${LAGDA}
	${LATEX}  ${DOC}
	${BIBTEX} ${DOC}
	${LATEX}  ${DOC}   # to make sure the (cross)references are correct
	${LATEX}  ${DOC}

figs:
	cd ${FIGS} && ${MAKE}


#----------------------------------------------------------------

again: 
	touch ${DOC}.lagda && ${MAKE}

clean:
	rm -f ${DOC}.tex *.aux *.log *.cov *.par *.bbl *.fls *.blg *.xml *.bcf *.dvi *.out *~

clean2: clean
	rm -f ${DOC}.pdf

v: ${PDF}
	acroread ${PDF}

