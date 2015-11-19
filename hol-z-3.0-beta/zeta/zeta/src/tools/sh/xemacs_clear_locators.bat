@echo off
set GNUDOIT=%ZETABASE%\lib\emacs\gnudoit
%GNUDOIT% "(progn (zeta-server-clear))"
