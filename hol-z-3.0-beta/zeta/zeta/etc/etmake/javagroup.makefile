#
# $Id: javagroup.makefile,v 1.5 1998/12/15 21:40:27 wg Exp $
# Robert Buessow, TU Berlin

ifndef __JAVAGROUP__
__JAVAGROUP	= __JAVAGROUP

include $(ET)/etc/etmake/java.makefile

#ifndef SUBJAVANODES
#SUBJAVANODES	= $(shell for f in *; do \
#			     [ -f $$f/ETMakefile -o -f "$$f/ETNodekind" ] && \
#			     echo $$f; \
#			  done \
#		   )
#endif

sources: javagroup_sources

javagroup_sources:
	@if [ -n "$(SUBJAVANODES)" ]; then \
	    for node in $(SUBJAVANODES) _x; do \
		[ $$node = "_x" ] || \
		(cd $$node 1>/dev/null 2>/dev/null && $(ETMAKE) -s sources) | \
		sed "s/\\([^ ][^ ]*\\)/$$node\\/\\1/g" ; \
	    done \
	fi

#| /usr/bin/sed /^/$$node/) \
#	@echo $(foreach node, $(SUBJAVANODES), \
#			      $(patsubst %, $(node)/%, \
#			      $(shell echo $(node) >&2; cd $(node); $(ETMAKE) sources; echo X $(node) >&2)))


boot:
	@args=`$(ETMAKE) -s sources`; \
	echo $(PIZZA) $$args >&2; \
	$(PIZZA) $$args 


#@#$(PIZZA) $(shell $(ETMAKE) sources)

endif
