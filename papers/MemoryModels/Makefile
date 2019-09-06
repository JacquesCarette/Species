all: mem.pdf

mem.pdf : latex/models.tex mem.tex
	latexmk -pdf mem.tex

latex/models.tex : models.lagda
	agda --allow-unsolved-metas --latex -i . models.lagda
