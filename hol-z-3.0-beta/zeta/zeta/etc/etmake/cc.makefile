#
# $Id: cc.makefile,v 1.6 2000/05/12 16:46:12 wg Exp $

ifndef __CC
__CC 		= __CC

CCCOMPILE = g++ $(CCFLAGS) -c -o 
CCCOMPILETOASM = g++ $(CCFLAGS) -fverbose-asm -S -c -o
CCLINK = g++ $(CCFLAGS) -o
CCLINKSHARED = g++ -shared $(CCFLAGS) -o
# CCLINKSHAREDLIBS = 

this:	cc_this
clear:  cc_clear


# C++ compilation

%.S : %.cpp $(patsubst %, %.h, $(HFILES))
	$(CCCOMPILETOASM) $*.S $*.cpp

%.o : %.cpp $(patsubst %, %.h, $(HFILES))
	$(CCCOMPILE) $*.o $*.cpp

# Linking

ifdef MAIN
$(MAIN): $(patsubst %, %.o, $(CFILES)) 
	$(CCLINK) $(MAIN) $(patsubst %, %.o, $(CFILES)) 	
endif

ifdef SHARED
$(SHARED): $(patsubst %, %.o, $(CFILES)) 
	$(CCLINKSHARED) $(SHARED) $(patsubst %, %.o, $(CFILES)) $(CCLINKSHAREDLIBS) 	
endif


# targets

cc_this: $(MAIN) $(SHARED)

cc_clear:
	rm -f $(MAIN) $(SHARED) $(patsubst %, %.o, $(CFILES))


cc_S: $(patsubst %, %.S, $(CFILES))
cc_C: $(patsubst %, %.o, $(CFILES))

endif
