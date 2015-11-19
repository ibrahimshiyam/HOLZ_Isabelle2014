#
# $Id: dataport.makefile,v 1.2 1998/11/30 17:46:31 buessow Exp $
# Robert Buessow, TU Berlin

ifndef __DATAPORT
__DATAPORT	= __DATAPORT

include $(ET)/etc/etmake/c.makefile

CPPFLAGS	:= $(CPPFLAGS) -I$(STM_ROOT)/include
LOADLIBES	:= $(LOADLIBES) $(STM_LIB)/dataport.o $(STM_LIB)/x_stubs.o
LDLIBS		= -R/usr/ucblib -L/usr/ucblib -lucb \
		   $(STM_LIB)/libgcc.a -lm -ldl

endif
