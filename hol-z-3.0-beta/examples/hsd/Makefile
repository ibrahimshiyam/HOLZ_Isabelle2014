#############################################################################
# HOL-Z --- a shallow embedding of Z into Isabelle/HOL
#             http://projects.brucker.ch/hol-z/
#                                                                            
# Makefile --- 
# This file is part of HOL-Z.
#
# Copyright (c) 2003-2007 ETH Zurich, Switzerland
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
# $Id: Makefile 6743 2007-08-03 06:39:08Z brucker $ 

#
#
#
#
TEXMFHOME       = {../../../lib/texmf}
export TEXMFHOME
include ../../../make.config

HOLZ_JAR = ../../../lib/holz.jar
CLASSPATH := $(HOLZ_JAR):$(CLASSPATH)
export CLASSPATH

all: pdf

zeta: HSD.tex
	$(LATEX) HSD
	makeindex HSD
	cp zetarc.template zetarc
	${ZETA} ${ZETA_FLAGS}
	mv *.holz holz
	mv *.ML holz
	rm -f zetarc

dvi: HSD.tex
	$(LATEX) HSD
	mv *.ML holz

pdf: HSD.tex
	#makeindex HSD
	$(LATEX) HSD
	mv *.ML holz

ac: 
	acroread HSD.pdf& 

bib: HSD.tex
	bibtex HSD

clean:
	rm -f holz/*.holz holz/*ML *~ *.log *.aux

distclean: clean
	rm -rf *.dvi holz/*.holz holz/*ML HSD-zdef.tex *.toc *.aux  *.idx *.check *.out
check:
	./proof-check.sh
