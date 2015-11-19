# ZETA Startup Script.
#
# Robert Buessow, TU Berlin
# $Id: etenv.sh,v 1.26 2000/07/22 14:38:50 wg Exp $
#
# This script is included by all ZETA wrapper scripts.
# It sets environment variables ($CLASSPATH, $LOAD_LIBRARY_PATH, etc) and 
# $JAVA

croak() {
    echo $* >&2; exit 1
}

[ -z "$ZETABASE" ] && croak "$0: \$ZETABASE not defined"

. $ZETABASE/etc/defaults.sh

# formerly ZETABASE was named ET. Still provide this is an alias
ET=$ZETABASE
export ET


ZETA_INSTALL=$ZETABASE/etc/et-install;		export ZETA_INSTALL
ET_INSTALL=$ZETABASE/etc/et-install;		export ET_INSTALL

JAVA_MAXHEAP=${JAVA_MAXHEAP:-64m}
JAVA_MAXNSTACK=${JAVA_MAXNSTACK:-32m}

# Set $LM_LICENSE_FILE for Statemate/Dataport.
if [ -n "$STM_ROOT" ]; then
  LM_LICENSE_FILE=$STM_ROOT/pm/license.dat${LM_LICENSE_FILE:+:$LM_LICENSE_FILE}
  export LM_LICENSE_FILE
fi

# configure these in your `default.sh' if you do not like 
# these default values.
MAKE=${MAKE:-gmake};                    export MAKE
GS=${GS:-gs};				export GS
PNMCROP=${PNMCROP:-pnmcrop};		export PPMCROP
PPMTOGIF=${PPMTOGIF:-ppmtogif};		export PPMTOGIF
PS2EPSI=${PS2EPSI:-ps2epsi};		export PS2EPSI
PSTOPS=${PSTOPS:-pstops};		export PSTOPS
SMV=${SMV:-smv};			export SMV
READLINE=${READLINE:-$ZETABASE/lib/readline}	export READLINE
XEMACS=${XEMACS:-xemacs};		export XEMACS
if [ -z "$GNUDOIT" ]
then
    GNUDOIT="gnudoit -q "
				    fi; export GNUDOIT
NOTANGLE=${NOTANGLE:-notangle};		export NOTANGLE
NOWEAVE=${NOWEAVE:-noweave};		export NOWEAVE
LATEX2HTML=${LATEX2HTML:-latex2html};	export LATEX2HTML

RM=${RM:-/bin/rm};			export RM
ECHO=${ECHO:-echo};			export ECHO
LN=${LN:-ln};				export LN
CP=${CP:-cp};				export CP
MKDIRHIER=${MKDIRHIER:-mkdirhier};	export MKDIRHIER
RMIC=${RMIC:-${JAVA_HOME}/bin/rmic}; export RMIC
JAVAC=${JAVAC:-${JAVA_HOME}/bin/javac}; export JAVAC
PIZZAC=${PIZZAC:-${ZETABASE}/bin/pc}; export PIZZAC
JNIINCLUDE=${JNIINCLUDE:-"-I${JAVA_HOME}/include \
			 -I${JAVA_HOME}/include/linux \
			 -I${JAVA_HOME}/include/solaris \
			 -I${JAVA_HOME}/include/genunix"}

export JNIINCLUDE
JAVAH=${JAVAH:-${JAVA_HOME}/bin/javah}; export JAVAH
SMLPATH=${SMLPATH:-/usr/local/smlnj/bin/sml}; export SMLPATH
ISAHEAP=${ISAHEAP:-$ZETABASE/lib/holz/HOL}; 	export ISAHEAP
ISAREMOTE=${ISAREMOTE:-""};   export ISAREMOTE

#LD_LIBRARY_PATH=$ZETABASE/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}
export LD_LIBRARY_PATH

CLASSPATH=$ZETABASE/classes${ADDCLASSPATH:+:$ADDCLASSPATH}
export CLASSPATH

JAVA="${JAVA:-${JAVA_HOME}/bin/java} \
      $JAVA_PROPERTIES -Xmx$JAVA_MAXHEAP -Xms$JAVA_MAXNSTACK"; export JAVA

JAVACC_HOME=${JAVACC_HOME:-"Please_set_JAVACC_HOME"}; export JAVACC_HOME
