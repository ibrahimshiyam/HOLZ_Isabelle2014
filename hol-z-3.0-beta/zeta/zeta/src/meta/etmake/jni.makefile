#
# $Id: jni.makefile,v 1.4 2000/03/13 06:57:11 wg Exp $
# Robert Buessow, TU Berlin

ifndef __JNI
__JNI		= __JNI

include $(ET)/etc/etmake/java.makefile
include $(ET)/etc/etmake/c.makefile

JAVAH		= $(JAVA_HOME)/bin/javah -jni
CPPFLAGS	:= $(CPPFLAGS) $(JNIINCLUDE)

ifndef LDD_SHARED
LDD_SHARED	= gcc -shared
endif

lib%.so: %.o
	$(LDD_SHARED) $*.o $(LOADLIBES) $(LDLIBS) -o lib$*.so

endif
