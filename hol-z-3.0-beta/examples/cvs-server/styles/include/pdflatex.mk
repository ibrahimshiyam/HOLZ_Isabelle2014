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
## $Id: pdflatex.mk,v 1.2 2002/05/23 11:36:16 brucker Exp $
##

.SUFFIXES:  .eps .ps .tex .pdf $(SUFFIXES)

.tex.pdf:
	$(RM) -f $*-zdef.tex
	$(PDFLATEX) $<
ifneq ($(DRAFT),yes)
	-@$(EGREP) -c 'Citation .* undef' $*.log && $(BIBTEX) $*;$(PDFLATEX) $* || true
	-@$(EGREP) -c 'Term .* not def' $*.log && $(BIBTEX) $*.gls;$(PDFLATEX) $* || true
	-@$(EGREP) -c 'Writing index file'  $*.log && $(MAKEINDEX) $(IDX_OPTIONS) $* || true
	-@$(EGREP) -c 'may have changed' $*.log && $(PDFLATEX) $* || true 
	-@$(EGREP) -c 'Rerun ' $*.log && $(PDFLATEX) $* || true
	-@$(EGREP) -c 'Citation .* undef' $*.log && $(BIBTEX) $*;$(PDFLATEX) $* || true
	-@$(EGREP) -c 'Term .* not def' $*.log && $(BIBTEX) $*.gls;$(PDFLATEX) $* || true
	-@$(EGREP) -c 'Writing index file'  $*.log && $(MAKEINDEX) $(IDX_OPTIONS) $* || true
	-@$(EGREP) -c 'may have changed' $*.log && $(PDFLATEX) $* || true 
	-@$(EGREP) -c 'Rerun ' $*.log && $(PDFLATEX) $*  || true
	-@$(EGREP) -c 'thumbpdf' $*.log && $(THUMBPDF) $* && $(PDFLATEX) $* || true
	$(EGREP) -c 'pause.sty' $*.log && $(JAVA) -jar $(PPOWER) $*.pdf $*_tmp.pdf && mv $*_tmp.pdf $*.pdf || true
	$(EGREP) -c 'pause.sty' $*.log && $(JAVA) -cp $(PPOWER) de.tu_darmstadt.sp.pdftools.ThumbGen $*.pdf $*_tmp.pdf && mv $*_tmp.pdf $*.pdf || true
else
	$(EGREP) -c 'pause.sty' $*.log && $(JAVA) -jar $(PPOWER) $*.pdf $*_tmp.pdf && mv $*_tmp.pdf $*.pdf || true
	@echo "DRAFT MODE: LaTeX was only startet _once_ and no thumbnails were created!"
endif

.tex.dvi:
	$(RM) -f $*-zdef.tex
	$(PDFLATEX) "\AtBeginDocument{\pdfoutput 0}" "\input{$*}" 
ifneq ($(DRAFT),yes)
	-@$(EGREP) -c 'Citation .* undef' $*.log && $(BIBTEX) $*;\
		$(PDFLATEX) "\AtBeginDocument{\pdfoutput 0}" "\input{$*}" || true
	-@$(EGREP) -c 'Term .* not def' $*.log && $(BIBTEX) $*.gls;\
		$(PDFLATEX) "\AtBeginDocument{\pdfoutput 0}" "\input{$*}" || true
	-@$(EGREP) -c 'Writing index file'  $*.log && $(MAKEINDEX) $(IDX_OPTIONS) $*\
		$(PDFLATEX) "\AtBeginDocument{\pdfoutput 0}" "\input{$*}" || true
	-@$(EGREP) -c 'may have changed' $*.log && \
		$(PDFLATEX) "\AtBeginDocument{\pdfoutput 0}" "\input{$*}" || true 
	-@$(EGREP) -c 'Rerun ' $*.log && \
		$(PDFLATEX) "\AtBeginDocument{\pdfoutput 0}" "\input{$*}" || true
	-@$(EGREP) -c 'Citation .* undef' $*.log && $(BIBTEX) $*;\
		$(PDFLATEX) "\AtBeginDocument{\pdfoutput 0}" "\input{$*}" || true 
	-@$(EGREP) -c 'Term .* not def' $*.log && $(BIBTEX) $*.gls;\
		$(PDFLATEX) "\AtBeginDocument{\pdfoutput 0}" "\input{$*}" || true
	-@$(EGREP) -c 'Writing index file'  $*.log && $(MAKEINDEX) $(IDX_OPTIONS) $*\
		$(PDFLATEX) "\AtBeginDocument{\pdfoutput 0}" "\input{$*}"  
	-@$(EGREP) -c 'may have changed' $*.log && \
		$(PDFLATEX) "\AtBeginDocument{\pdfoutput 0}" "\input{$*}" || true
	-@$(EGREP) -c 'Rerun ' $*.log && \
		$(PDFLATEX) "\AtBeginDocument{\pdfoutput 0}" "\input{$*}" || true 
else
	@echo "DRAFT MODE: LaTeX was only startet _once_!"
endif
.tex.bbl:
	$(BIBTEX) ${DOCUMENT}
.dvi.eps:
	$(DVIPS) -E $< -o $@
.dvi.ps:
	$(DVIPS) -P pdf $< -o $@
	
