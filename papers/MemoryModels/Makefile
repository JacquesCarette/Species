all: mem.pdf

mem.pdf : latex/models.tex mem.tex
	stack exec -- latexmk -e '$$pdflatex=q/pdflatex %O -shell-escape %S/' -pdf mem.tex

latex/models.tex : models.lagda
	agda --latex -i . models.lagda
