.PHONY: all clean distclean

all:
	latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

clean:
	latexmk -c

distclean:
	latexmk -C
	rm -f *.synctex.gz
