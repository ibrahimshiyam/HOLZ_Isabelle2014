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
## netpbm.mk,v 1.1 2001/11/05 09:16:29 brucker Exp
##
ANY2PNM   = anytopnm
PNM2PS    = pnmtops
PNM2PNG   = pnmtopng

.SUFFIXES:  .pnm .eps .tif .gif .jpg .pbm .pgm .ppm .ps .png $(SUFFIXES)

.tif.pnm:
	${ANY2PNM} $< > $@
.gif.pnm:
	${ANY2PNM} $< > $@
.jpg.pnm:
	${ANY2PNM} $< > $@
.jpeg.pnm:
	${ANY2PNM} $< > $@
.png.pnm:
	${ANY2PNM} $< > $@
.gem.pnm:
	${ANY2PNM} $< > $@
.palm.pnm:
	${ANY2PNM} $< > $@
.pnm.png: 
	${PNM2PNG} $< > $@
.pnm.eps:
	${PNM2PS} -noturn $< > $@
.pbm.eps:
	${PNM2PS} -noturn $< > $@
.pgm.eps:
	${PNM2PS} -noturn $< > $@
.ppm.eps:
	${PNM2PS} -noturn $< > $@
