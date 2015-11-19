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
## magick.mk,v 1.1 2001/11/05 09:16:29 brucker Exp
##
CONVERT   = convert

.SUFFIXES:  .pnm .eps .tif .gif .jpg .pbm .pgm .ppm .ps .png $(SUFFIXES)

.tif.eps:
	${CONVERT} $< $@
.gif.eps:
	${CONVERT} $< $@
.jpg.eps:
	${CONVERT} $< $@
.jpeg.eps:
	${CONVERT} $< $@
.png.eps:
	${CONVERT} $< $@
.gem.eps:
	${CONVERT} $< $@
.palm.eps:
	${CONVERT} $< $@
.pnm.eps:
	${CONVERT} $< $@
.pbm.eps:
	${CONVERT} $< $@
.pgm.eps:
	${CONVERT} $< $@
.ppm.eps:
	${CONVERT} $< $@

.tif.png:
	${CONVERT} $< $@
.gif.png:
	${CONVERT} $< $@
.jpg.png:
	${CONVERT} $< $@
.jpeg.png:
	${CONVERT} $< $@
.gem.png:
	${CONVERT} $< $@
.palm.png:
	${CONVERT} $< $@
.pnm.png: 
	${CONVERT} $< $@
.pbm.png:
	${CONVERT} $< $@
.pgm.png:
	${CONVERT} $< $@
.ppm.png:
	${CONVERT} $< $@
