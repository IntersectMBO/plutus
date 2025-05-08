all:
	agda-with-stdlib --latex system-f-in-agda.lagda --latex-dir .
	latexmk -pdf system-f-in-agda.tex

clean:
	latexmk -C && rm -f *.bbl *.nlo *.nls *.ist *.thm *.sty *.ptb 

