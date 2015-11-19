#
# $Id: javacc.makefile,v 1.4 1999/01/13 12:44:38 buessow Exp $
# Robert Buessow, TU Berlin

ifndef __JAVACC
__JAVACC		= __JAVACC

include $(ET)/etc/etmake/java.makefile

ifndef JAVACC_HOME
    JAVACC_HOME		= $(JAVA_HOME)
endif

ifndef JAVACC
JAVACC			= $(JAVACC_HOME)/bin/javacc
endif

ifndef JAVACC_FILES
JAVACC_FILES		= $(wildcard *.jj)
endif

JAVACC_GENERATED        := $(JAVACC_FILES:%.jj=%Constants.java) \
                           $(JAVACC_FILES:%.jj=%.java) \
                           TokenMgrError.java Token.java \
                           ParseException.java

ifndef JAVACC_USER_TOKEN_MANAGER
  JAVACC_GENERATED      += $(JAVACC_FILES:%.jj=%TokenManager.java)
  ifndef JAVACC_UNICODE_ESCAPE
    JAVACC_GENERATED    += SimpleCharStream.java
  else
    JAVACC_GENERATED    += JavaCharStream.java
  endif
else
  JAVACC_GENERATED      += TokenManager.java
endif

_JAVA_FILES		:= $(JAVA_FILES)
JAVA_FILES		:= $(_JAVA_FILES) $(JAVACC_GENERATED)

sources:                $(JAVACC_FILES:%.jj=%.java)


$(JAVA_STATE_FILE): $(JAVACC_FILES:%.jj=%.java)

.PHONY: javacc_clean

%.java: %.jj
	$(JAVACC) $*.jj

clean: javacc_clean

javacc_clean:
	rm -f $(JAVACC_GENERATED)

endif
