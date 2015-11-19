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
## postscript.mk,v 1.1 2001/11/05 09:16:29 brucker Exp
##

.SUFFIXES:  .eps .ps .pdf $(SUFFIXES)

.ps.eps:
	$(PS2EPS) $< $@
.eps.pdf:
	$(EPS2PDF) --outfile=$@ $< 
.ps.pdf:
	$(PS2PDF) $< $@
#.pdf.ps:
#	$(PDF2PS) $< $@
#.pdf.eps:
#	$(PDF2EPS) $< $@
