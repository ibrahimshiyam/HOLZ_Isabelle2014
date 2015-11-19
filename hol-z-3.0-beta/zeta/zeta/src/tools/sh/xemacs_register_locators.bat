@echo off
set GNUDOIT=%ZETABASE%\lib\emacs\gnudoit
%GNUDOIT% (progn (zeta-server-register '((\"%1\" %2 %3 %4 %5))))
