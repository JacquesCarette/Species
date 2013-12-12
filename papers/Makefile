all: SpeciesAsConstructors.pdf

SpeciesAsConstructors.pdf: SpeciesAsConstructors.tex
	pdflatex SpeciesAsConstructors
	bibtex SpeciesAsConstructors
	pdflatex SpeciesAsConstructors
	pdflatex SpeciesAsConstructors

SpeciesAsConstructors.tex: SpeciesAsConstructors.lhs
	lhs2tex SpeciesAsConstructors.lhs > SpeciesAsConstructors.tex
