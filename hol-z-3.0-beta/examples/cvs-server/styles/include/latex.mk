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
## latex.mk,v 1.1 2001/11/05 09:16:29 brucker Exp
##

.SUFFIXES:  .eps .ps .tex .pdf $(SUFFIXES)

.tex.dvi:
	$(LATEX) $<
ifneq ($(DRAFT),yes)
	-@$(EGREP) -c 'Citation .* undef' $*.log && $(BIBTEX) $*;$(LATEX) $* || true
	-@$(EGREP) -c 'Term .* not def' $*.log && $(BIBTEX) $*.gls;$(LATEX) $* || true
	-@$(EGREP) -c 'Writing index file'  $*.log && $(MAKEINDEX) $(IDX_OPTIONS) $* || true
	-@$(EGREP) -c 'may have changed' $*.log && $(LATEX) $*  || true
	-@$(EGREP) -c 'Rerun ' $*.log && $(LATEX) $*  || true
	-@$(EGREP) -c 'Citation .* undef' $*.log && $(BIBTEX) $*;$(LATEX) $* || true
	-@$(EGREP) -c 'Term .* not def' $*.log && $(BIBTEX) $*.gls;$(LATEX) $* || true
	-@$(EGREP) -c 'Writing index file'  $*.log && $(MAKEINDEX) $(IDX_OPTIONS) $* || true
	-@$(EGREP) -c 'may have changed' $*.log && $(LATEX) $* || true 
	-@$(EGREP) -c 'Rerun ' $*.log && $(LATEX) $* || true
else
	@echo "DRAFT MODE: LaTeX was only startet _once_!"
endif
	      
.tex.bbl:
	$(BIBTEX) ${DOCUMENT}
.dvi.eps:
	$(DVIPS) -E $< -o $@
.dvi.ps:
	$(DVIPS) -P www $< -o $@
