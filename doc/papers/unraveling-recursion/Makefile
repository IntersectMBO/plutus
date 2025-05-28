all:
	for f in *.lagda; do \
		agda-with-stdlib --latex $$f --latex-dir .; \
	done
	latexmk -pdf unraveling-recursion.tex

clean:
	latexmk -C && rm -f *.bbl *.nlo *.nls *.ist *.thm *.sty *.ptb *.agdai