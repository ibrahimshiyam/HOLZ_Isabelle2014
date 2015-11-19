#
# $Id: c.makefile,v 1.5 1998/12/15 12:06:11 buessow Exp $
# Robert Buessow, TU Berlin

ifndef __C
__C 		= __C

CC		= gcc
CFLAGS		= -Wall -Werror -fpic
COMPILE.c 	= $(CC) $(CFLAGS) $(CPPFLAGS) $(TARGET_ARCH) -c
LINK.o 		= $(CC) $(LDFLAGS) $(TARGET_ARCH)



%.o: %.c
	$(COMPILE.c) $< $(OUTPUT_OPTION)

%: %.o
	$(LINK.o) $^ $(LOADLIBES) $(LDLIBS) -o $@

endif
