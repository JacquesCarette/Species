all: mem.pdf

mem.pdf : latex/models.tex mem.tex MemDiagrams.hs
	stack exec -- latexmk -e '$$pdflatex=q/pdflatex %O -shell-escape %S/' -pdf mem.tex

latex/models.tex : models.lagda format.sed
	agda --latex -i . models.lagda
	sed -f format.sed $@ > latex/models.sedded
	mv latex/models.sedded $@
