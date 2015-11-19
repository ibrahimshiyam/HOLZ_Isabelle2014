@echo off 

REM you need to set this variable to point to ZETAs installation base
rem set ZETABASE=e:\et
set ZETABASE=u:\et
set ET=%ZETABASE%
set STM_ROOT=C:\Programme\i-Logix\Statemate Magnum
set LM_LICENSE_FILE=%STM_ROOT%\pm\license.dat
set TEXBASE=C:\texmf
set PSTOPS=%TEXBASE%\miktex\bin\pstops.exe
set PNMCROP=%TEXBASE%\miktex\bin\pnmcrop.exe
set PS2EPSI=C:\Programme\gstools\gs5.50\ps2epsi.bat

REM you need to set this variable to point to the java interpreter
set JAVA_HOME=c:\jdk1.2
set JAVA=%JAVA_HOME%\bin\java



REM ------------------------------------------------------------------
REM END OF CONFIGURATION PART

set JAVACLASSES=%ZETABASE%\classes
set CYGWIN=c:\Program Files\cygnus\cygwin-b20

IF NOT EXIST ZETA mkdir ZETA

set PATH=%PATH%;%STM_ROOT%\lib;%TEXBASE%\miktex\bin
set TEXINPUTS=.;%ZETABASE%\lib\latex;

%JAVA% -Dzeta.stmps2eps=et-stmps2eps.bat -Dzeta.local-dataport=true -classpath %ZETABASE%\classes -Djava.library.path=%ZETABASE%\lib -Dzeta.tmpdir="c:\temp" -Dzeta.home=%ZETABASE% -Dzeta.debug.zap.keep=yes -Dzeta.latex.path=%ZETABASE%\lib\ztoolkits zeta.tools.sh.GuiCommander ZETA
