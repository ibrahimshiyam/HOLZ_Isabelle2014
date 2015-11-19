#############################################################################
# HOL-Z --- a shallow embedding of Z into Isabelle/HOL
#             http://projects.brucker.ch/hol-z/
#                                                                            
# Makefile --- 
# This file is part of HOL-Z.
#
# Copyright (c) 2000-2002 University Freiburg, Germany
#
# HOL-Z is free software; you can redistribute it and/or modify it under   
# the terms of the GNU General Public License as published by the Free       
# Software Foundation; either version 2 of the License, or (at your option)  
# any later version.                                                         
#                                                                            
# HOL-Z is distributed in the hope that it will be useful, but WITHOUT ANY 
# WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS 
# FOR A PARTICULAR PURPOSE. See the GNU General Public License for more 
# details.                                                              
#                                                                            
# You should have received a copy of the GNU General Public License along    
# with this program; if not, write to the Free Software Foundation, Inc.,    
# 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.                  
##############################################################################
# $Id: Makefile 6745 2007-08-03 06:43:21Z brucker $ 

TEXMFHOME           = {../../../lib/texmf,./styles/,./styles/}
export TEXMFHOME
include ../../../make.config

HOLZ_JAR = ../../../lib/holz.jar
CLASSPATH := $(HOLZ_JAR):$(CLASSPATH)

export CLASSPATH

#DRAFT=yes

## 1) Document specific configuration
## ==================================
BASEDIR      = .
BIBFILES     =
BSTFILES     =
GRAPHICS     =
PIC          = pics/arch_overview.comb  \
                  pics/attack.comb \
                  pics/mapping_overview.comb \
                  pics/hierarchy.comb \
                  pics/ref_sec1.pdf \
                  pics/ref_sec2.pdf \
                  pics/ref_sec3.pdf \
                  pics/arch_overview1.pdf \
                  pics/arch_overview2.pdf \
                  pics/arch_overview3.pdf \
                  pics/arch_overview4.pdf \
		  pics/ids.pdf\
		  pics/ref_concept1.comb\
		  pics/ref_concept2.comb\
		  pics/toolchain.comb
DOCUMENT     =arch
SOURCES      =
AUTHOR       =
DIRECTORIES  = 
IDX_OPTIONS     = -s ./styles/default 
##
## 2) LaTeX specific Path configuration
## ====================================
BIBINPUTS      := ${BIBINPUTS}:${BASEDIR}/bibliography/database:${BASEDIR}/glossary
TEXINPUTS      := ./styles:${TEXINPUTS}:./styles
##
## 3) Configure default target
## ===========================
## this should be one of ${DOCUMENT}.dvi, ${DOCUMENT}.ps, ${DOCUMENT}.pdf
all: ${DOCUMENT}.pdf zeta
# all: ${DOCUMENT}.ps
# all: ${DOCUMENT}.dvi
##
## 4) Use LaTeX or pdfLaTeX
LOGFILES = ${DOCUMENT}.log $(FILES:%=%.log)
AUXFILES = $(DOCUMENT).aux $(FILES:%=%.aux)
IDXFILES =  
##
## 4) Path and program specific configuration
## ==========================================
LATEX      = elatex
PDFLATEX   = pdfelatex
THUMBPDF   = thumbpdf
BIBTEX     = bibtex
BIBTOOL    = bibtool
MAKEINDEX  = makeindex
CHKTEX     = chktex
LACHECK    = lacheck
DVIPS      = dvips
EPS2PDF    = epstopdf
PS2PDF     = ps2pdf
GREP       = grep
EGREP      = egrep
FIG2DEV    = fig2dev 
THUMBPDF   = thumbpdf
RM         = rm
LN         = ln
MV   	   = mv	
SED        = sed
LATEX2HTML = latex2html
WWWBROWSER = netscape
JAVA       = java
PPOWER4    = $(BASEDIR)/texmf/ppower4/pp4pb.jar
#############################################################################
## No user configuration needed below this line                          ####
#############################################################################
##
## 7) Module selection
## ===================
#include $(BASEDIR)/styles/include/latex.mk
include $(BASEDIR)/styles/include/netpbm.mk
include $(BASEDIR)/styles/include/pdflatex.mk
include $(BASEDIR)/styles/include/postscript.mk
include $(BASEDIR)/styles/include/graphivz.mk
# include $(BASEDIR)/styles/include/magick.mk
include $(BASEDIR)/styles/include/check.mk
include $(BASEDIR)/styles/include/xfig.mk
##
## 6) Environment initialization and main rules
## ============================================
export TEXMF BIBINPUTS INDEXSTYLE TEXINPUTS
.PHONY = .clean .distclean
${DOCUMENT}.pdf: $(SOURCES) $(PIC) $(GRAPHICS)
${DOCUMENT}.ps:  $(SOURCES) $(PIC) $(GRAPHICS)
${DOCUMENT}.dvi: $(SOURCES) $(PIC) $(GRAPHICS)
${DOCUMENT}_html: $(SOURCES) $(PIC) $(GRAPHICS)
${DOCUMENT}.idx: ${DOCUMENT}.tex $(SOURCES)
	$(LATEX) $<
${DOCUMENT}.ind: ${DOCUMENT}.idx
	$(MAKEINDEX) $(IDX_OPTIONS) $<
zeta: ${DOCUMENT}.pdf	
	sed 's/ {/{/g' < arch-zdef.tex > x.tex
	sed 's/ }/}/g' < x.tex > arch-zdef.tex
	mv x.tex arch-zdef.tex
	cp zetarc.template zetarc
	${ZETA} ${ZETA_FLAGS}
	mv *.holz holz
	rm zetarc
soffice:
	/home/brucker/bin/zeta2xx arch.tex
clean:
	$(RM) -f $(AUXFILES) $(LOGFILES)
	$(RM) -f $(IDXFILES)
	$(RM) -rf $(DOCUMENT) $(PIC)
	$(RM) -f *info *.tpt
	$(RM) -f *-zdef.tex *.check
	$(RM) -f *.rel *.idx *.lot *.ind *.ilg *.lof *.thm *.html *.toc *.out *.tmp  *.log *.bak *.aux *.bbl *.blg  *.eps *~
distclean: clean
	$(RM) -f *.dvi *.ps holz/*.holz

