#############################################################################
# HOL-Z --- a shallow embedding of Z into Isabelle/HOL
#             http://projects.brucker.ch/hol-z/
#                                                                            
# Makefile --- 
# This file is part of HOL-Z.
#
# Copyright (c) 2000-2003 University Freiburg, Germany
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
##############################################################################)
# $Id: Makefile 6738 2007-08-03 06:13:12Z brucker $ 

TEXMFHOME           = {../../../lib/texmf}
export TEXMFHOME
include ../../../make.config
BIBTEX = bibtex

HOLZ_JAR = ../../../lib/holz.jar
CLASSPATH := $(HOLZ_JAR):$(CLASSPATH)
export CLASSPATH

zeta: *.tex
	cp zetarc.template zetarc
	${ZETA} ${ZETA_FLAGS}
	mv *.holz holz
	rm zetarc

dvi: *.tex
	$(LATEX) model
	$(BIBTEX) model
	$(LATEX) model
	$(LATEX) model

clean:
	rm -f *.holz *~ *.aux *.log *. 
	rm -f model.bbl model.blg model.brf model.idx model.toc

distclean: clean
	rm -rf holz/*.holz

