#
# $Id: java.makefile,v 1.10 2000/07/22 07:53:17 wg Exp $
# Robert Buessow, TU Berlin

ifndef __JAVA
__JAVA		= __JAVA

ifndef PIZZA_HOME
    PIZZA_HOME	= $(JAVA_HOME)
endif

JAVACLASSDIR	= $(ZETABASE)/classes
JAVAC		:= $(JAVAC) -d $(JAVACLASSDIR) $(JAVAFLAGS)
PIZZA		= $(PIZZAC) -d $(JAVACLASSDIR) $(JAVAFLAGS)
PIZZADOC	= $(PIZZAC) -pizzadoc -d $(ZETABASE)/doc/api \
		  $(PIZZADOCFLAGS)
JAVADOC	        = javadoc -d $(ZETABASE)/doc/api \
		  $(JAVADOCFLAGS)

PIZZADOCFLAGS	= -author -sourceversion -index -tree
JAVADOCFLAGS 	= -author -version -splitindex -use -package

JAVA_STATE_FILE = .etstate.java
LAST_JAVA_STATE	= $(shell [ ! -f $(JAVA_STATE_FILE) ] || cat $(JAVA_STATE_FILE))

#ifndef JAVA_FILES
#JAVA_FILES	= $(wildcard *.java)
#endif
#ifndef PIZZA_FILES
#PIZZA_FILES	= $(wildcard *.pizza)
#endif

ifndef JAVA_COMPILE
JAVA_COMPILE	= $(JAVA_FILES) $(PIZZA_FILES)
endif
ifndef COMPILE.java
COMPILE.java	= $(strip $(PIZZA) $(JAVA_COMPILE))
endif

COMPILE.rmic    = $(RMIC) -d $(JAVACLASSDIR)

.PHONY: java_doc java_force 
.SILENT: java_state java_force

this: java_this

java_this: $(JAVA_STATE) $(JAVA_STATE_FILE) rstubs

ifdef JAVA_REMOTE_STUBS
rstubs:
	$(COMPILE.rmic) $(JAVA_REMOTE_STUBS)
else
rstubs:
endif

# $(JAVA_COMPILE)==java_state by default and ==java_force if -force
# option was selected
java_state:
	[ "$(LAST_JAVA_STATE)" = "$(strip $(COMPILE.java))" ] || rm -f $(JAVA_STATE_FILE)

java_force:
	rm -f $(JAVA_STATE_FILE)

$(JAVA_STATE_FILE): $(JAVA_COMPILE)
	@if [ -z "$(strip $(JAVA_COMPILE))" ]; then \
	    echo "nothing to do for java" ;  \
	else  \
	    echo $(COMPILE.java); \
	    $(COMPILE.java) && (echo $(COMPILE.java) > $(JAVA_STATE_FILE)); \
	fi


clear_state: 
	rm -f $(JAVA_STATE_FILE)
	@TARGET=clear_state $(VISITSUBS)

doc: pizza_doc

pizza_doc:
	[ -z "$(strip $(JAVA_COMPILE))" ] || $(PIZZADOC) $(JAVA_COMPILE)

jdoc: 
	[ -z "$(strip $(JAVA_COMPILE))" ] || $(JAVADOC) $(JAVA_COMPILE)

sources:
	@echo etmake: Collecting sources \``pwd`\' >&2
	@echo $(JAVA_FILES) $(PIZZA_FILES)

%.pizzac: %.pizza
	$(PIZZA) $*.pizza

%.javac: %.java
	$(PIZZA) $*.java

endif
