# ZETA developer settings.  
#
# $Id: defaults-form.sh,v 1.2 1998/11/25 07:56:59 wg Exp $
#

########################################################################
# REQUIRED SETTINGS 

  # Path of the Java installation.  ZETA assumes that Java, JavaCC (only
  # for developers), and Pizza (only for developers) is installed here.

#JAVA_HOME=/usr/lib/fjsdk
#export JAVA_HOME

  # Classpath. The pizza compiler requires to include here also
  # the standard classes for jdk1.2.

ADDCLASSPATH=${ZETABASE}/../pizza/pizza-1.1.jar
export ADDCLASSPATH

  # Path to the JavaCC installation (http://www.metamata.com)
JAVACC=javacc
export JAVACC

EMACS=emacs

########################################################################
# OPTIONAL SETTINGS

  # XEmacs
# XEMACS=xemacs

  # How to execute XEmacs gnuclient in batch mode
  # Appended is the form to execute
# GNUDOIT="gnuclient -q -batch -eval "

  # Gnu make.  
MAKE=make

  # ...  (see also etenv.sh)
