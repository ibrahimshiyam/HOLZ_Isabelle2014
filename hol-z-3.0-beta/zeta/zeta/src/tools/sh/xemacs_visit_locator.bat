@echo off
set GNUDOIT=%ZETABASE%\lib\emacs\gnudoit
%GNUDOIT% (progn (zeta-server-visit \"%1\" %2 %3 %4 %5))
