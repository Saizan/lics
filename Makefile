# Makefile for contnorm

destdir=$(HOME)/public_html

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { editor }' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }' \
	  -- 'delete.field = { doi }' \
	  -- 'delete.field = { url }'
catcfg=sed -e "s/%.*//g" <
pdflatex=pdflatex
# pdflatex=xelatex
stdlib=$(HOME)/tmp/Agda2/std-lib/src
sedfile=postprocess.sed
stylefile=latex/agda.sty

bibliography=short.bib

# All dependencies
files=icfp.bib macros.tex

allfiles=Makefile paper.lagda paper.tex paper.bbl auto-paper.bib $(files)

.PRECIOUS : %.tex latex/%.tex paper.pdf auto-paper.bib

default : paper.pdf

force :
	rm -f paper.aux
	lhs2TeX --agda --poly paper.lagda -o paper.tex
	pdflatex paper.tex
	bibtex paper.aux
	pdflatex paper.tex
	pdflatex paper.tex

ship : $(destdir)/paper.pdf $(destdir)/paper.zip

$(destdir)/%.pdf : %.pdf
	cp -p $< $@

$(destdir)/%.zip : %.zip
	cp -p $< $@

pack : paper.zip

paper.zip : $(allfiles)
	zip $@ $^

# paper
##################################################################

paper.tex : paper.lagda
	lhs2TeX --agda --poly paper.lagda -o paper.tex

# # initially, run latex once to create an .aux file
# # mark .aux file as fresh by creating a stamp _aux
paper_aux : paper.tex $(files)
	-$(pdflatex) paper.tex;
	touch $@;

# then, run bibtex
paper.bbl : paper_aux auto-paper.bib
	-bibtex paper;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
paper.pdf : paper.bbl
	-$(pdflatex) paper.tex;
	$(pdflatex) paper.tex;

# auto-paper.bib is only defined if bibtool is present
# and $(bibliography) exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-paper.bib : paper_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x paper.aux -i $(bibliography) >> $@;
endif
endif

# Templates

%.tex : latex/%.tex $(sedfile)
	sed --file=$(sedfile) < $< > $@

latex/%.tex : %.lagda
	agda --latex -i. -i$(stdlib) $< +RTS -M1.5g -RTS

# clean

clean :
	-rm $(generatedfiles)

cleaner :
	-rm $(generatedfiles)
	-cd latex; rm $(generatedfiles); cd ..

# EOF
