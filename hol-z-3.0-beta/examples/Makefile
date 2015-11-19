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
# $Id: Makefile 6732 2007-08-03 05:48:44Z brucker $ 

#EXAMPLES=bbook steamboiler hsd cvs-server leplas corbasec 
# Currently ported status: works till hsd (without proofs).
# cvsserver is reorganized for HOL-Z, but crashes
# due to loader problem.
# leplas and corbasec not arrasnged for HOL-Z 3.0

EXAMPLES=bbook steamboiler hsd

.PHONY: examples clean distclean

#examples: 
#	for dir in $(EXAMPLES); do $(MAKE) -C $$dir ; done
all:
	for dir in $(EXAMPLES); do cd $$dir; isatool make; cd ".."; done

clean:
	for dir in $(EXAMPLES); do $(MAKE) -C $$dir clean ; done
distclean:
	for dir in $(EXAMPLES); do $(MAKE) -C $$dir distclean ; done
