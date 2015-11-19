## Makefile for LaTeX
## 
## Copyright (c) 2001 Achim D. Brucker <brucker@informatik.uni-freiburg.de>
## All rights reserved.
## 
## This program is free software; you can redistribute it and/or modify 
## it under the terms of the GNU General Public License as published by 
## the Free Software Foundation; either version 2 of the License, or 
## (at your option) any later version.
##
## xfig.mk,v 1.2 2001/11/22 11:11:50 brucker Exp
##
FIG2DEV  = fig2dev

.PHONY: %.comb
.PRECIOUS: %_t.pdf
.SUFFIXES:  .comb _t.pdf .t_ps .fig .ps .eps .tex .pdf $(SUFFIXES)

CLEANFILES := $(PIC:%.comb=%.tex) $(PIC:%.comb=%_t.pdf) $(CLEANFILES)

%.comb: %_t.pdf %.tex  
	
.fig.ps:
	$(FIG2DEV) -L ps  $< $@
.fig.eps:
	$(FIG2DEV) -L eps $< $@
.fig.pdf:
	$(FIG2DEV) -L pdf $< $@

.fig.pic:
	$(FIG2DEV) -L latex $< $@
.fig.pstex:
	$(FIG2DEV) -L pstex  $< $@
.fig_t.pdf:
	$(FIG2DEV) -L pstex   -p $* $< > $*.ps
	$(EPS2PDF) -o $*_t.pdf $*.ps 
	$(RM) -f $*.ps
.fig.tex:
	$(FIG2DEV) -L pstex_t -p $*_t $< \
	| $(SED) -e 's/epsfig{file=/includegraphics{/' \
	| $(SED) -e 's/\\special{ps: grestore}//' \
	| $(SED) -e 's/\\special{ps: gsave [0-9] [0-9] [0-9] setrgbcolor}//' > $*.tex 
