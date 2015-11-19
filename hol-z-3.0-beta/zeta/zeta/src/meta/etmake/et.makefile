#
# $Id: et.makefile,v 1.8 2000/07/22 07:53:17 wg Exp $
# Robert Buessow, TU Berlin

ifndef ZETABASE
    ZETABASE	= $(ET)
endif

all: _all this

SUBNODES	= $(shell for f in *; do \
			     [ -f $$f/ETMakefile -o -f "$$f/ETNodekind" ] && \
			     echo $$f; \
			  done \
		   )


ifndef AUTOSUBNODES
AUTOSUBNODES	= $(SUBNODES)
endif

VISITSUBS	= $(foreach node,  \
		            $(AUTOSUBNODES),  \
		            ; (cd $(node) && $(ETMAKE) $$TARGET) \
		   )

# If NODEKIND was set by an ETNodekind file, include node kind
# specific makefiles before local ETMakefiles.
ifdef NODEKIND
    NODEKIND	:= $(NODEKIND:%=$(ET)/etc/etmake/%.makefile)
    include $(NODEKIND)
endif

NODEKIND 	=

# Include ETMakefile:
#
# ETMakefile.local overrides ETMakefile.  Note that ETMakefile.local
# is for personal, temporary changes such as `JAVA_FLAGS = -g' etc.
# ETMakefile.local should include ETMakefile and is not subject to
# version control.
ifeq ($(shell [ -f ETMakefile.local ] && echo yes), yes)
    include ETMakefile.local
else
    ifeq ($(shell [ -f ETMakefile ] && echo yes), yes)
	include ETMakefile
    endif
endif

ifdef NODEKIND 
    NODEKIND	:= $(NODEKIND:%=$(ET)/etc/etmake/%.makefile)
    include $(NODEKIND)
endif
 

.PHONY: all _all cleanall _cleanall dependall _dependall depend docall \
	_docall doc this _sources sources
.SILENT: _all _cleanall _depenall _docall _install _sources


_all:
	TARGET=all $(VISITSUBS)

cleanall: _cleanall clean
_cleanall:
	TARGET=cleanall $(VISITSUBS)

cleanstate: _cleanstate
_cleanstate:
	TARGET=cleanstate $(VISITSUBS)

# Give make some work, if no `sources' target is defined.
sources: _sources
_sources:
	@echo

install: inst _install
_install:
	TARGET=install $(VISITSUBS)

dependall: _dependall depend
	TARGET=dependall $(VISISUBS)

docall: _docall doc
_docall:
	TARGET=docall $(VISITSUBS)

inst: _inst
_inst:
	@if [ -n "$(INSTALL_LIBS)" ]; then \
	    $(ET_INSTALL) lib $(INSTALL_LIBS); \
	fi

